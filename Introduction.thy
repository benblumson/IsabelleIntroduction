(*<*)
theory Introduction (* NOTE: the name of the theory must exactly match the name of this file. *)
imports Main
begin
(*>*)

text {* \epigraph{It is unworthy of excellent men to lose hours like slaves in the labour of calculation which could 
safely be relegated to anyone else if machines were used.}{Liebniz @{cite "smith_source_1959"} p. 181.} *}

text {* This is an introduction to the Isabelle proof assistant aimed at philosophers and students
of philosophy.\footnote{I found a very useful introduction to be Nipkow @{cite "nipkow_tutorial_2011"}.
Another still helpful, though unfortunately dated, introduction is Grechuk @{cite "grechuk_isabelle_2010"}.
A person wishing to know how Isabelle works might first consult Paulson @{cite "paulson_ml_1996"}.
For the software itself and comprehensive documentation, see @{url "https://isabelle.in.tum.de/"}.
Isabelle might not be the right tool for your project -- for a comparison of alternatives see
Wiedijk @{cite "wiedijk_seventeen_2006"}.} *}

section {* Propositional Logic \label{propositional} *}

text {* Imagine you are caught in an air raid in the Second World War. You might reason as follows:
\begin{quotation}
Either I will be killed in this raid or I will not be killed. Suppose that I will. The even if I take
precautions, I will be killed, so any precautions I take will be ineffective. But suppose I am not
going to be killed. Then I won't be killed even if I neglect all precautions; so on this assumption,
no precautions are necessary to avoid being killed. Either way, any precautions I take will be either
ineffective or unnecessary, and so pointless.\footnote{This example is from Dummett @{cite "dummett_bringing_1964"} p. 345,
but the version quoted here is from Stalnaker @{cite "stalnaker_indicative_1975"} p. 280.}
\end{quotation} The example is notable for two reasons. *}

text {* First, if the argument were successful, then it would establish a version of \emph{fatalism},
according to which we cannot influence future events. Any future event will either happen or not. If
it happens then, according to the argument, it will happen even if I try to prevent it. On the other
hand, if it doesn't happen, then it won't happen regardless of whether I try to prevent it. Either
way, trying to prevent it is pointless. And the same goes for trying to prevent or bring about any
other future event. *}

text {* Second, and more importantly for our purposes, the argument is an example of a style emulated
by the natural deduction rules for propositional logic.\footnote{For a classic introduction to logic 
based on natural deduction, see Lemmon @{cite "lemmon_beginning_1965"}.} In this system, each propositional connective
is associated with two rules: an introduction rule, which allows you to introduce it into an argument, 
and an elimination rule, which allows you to derive something from it. Proofs in Isabelle are presented
using natural deduction, so knowing the introduction and elimination rules is all you need to understand
the proofs.\footnote{This part of the Isabelle system is known as ``Isar'' for ``Intelligible Semi-Automated Reasoning'' 
See Wenzel @{cite "wenzel_isabelle/isarversatile_2002"}.} We will take the rules for each connective in turn. *}

subsection {* Conditionals *}

text {* Conditionals are translated using an arrow. So ``if it's raining then it's cloudy'', for
example, is translated @{term "A \<longrightarrow> B"}, where @{term "A"} stands for ``it's raining'' and @{term "B"}
stands for ``it's cloudy''. The right hand side, in this case ``it's cloudy'', is known as the
``consequent'' -- since it's the consequence of the condition -- whereas the left had side, in this
case ``it's raining'' is known as the antecedent -- since it's the condition upon which the consequent
obtains. The next two subsections explain the introduction and elimination rules for conditionals. *}

subsubsection {* Conditional Proof \label{conditional_proof} *}

text {* According to the introduction rule for conditionals, sometimes known as ``conditional proof'',
in order to prove a conditional one must assume the antecedent and show the consequent. Here is the
very simplest example: *}

lemma "A \<longrightarrow> A"
proof (rule impI)
  assume "A"
  then show "A".
qed

text {* There are a few things to note about this example. The first line simply states the lemma to
be proved -- in this case @{term "A \<longrightarrow> A"}. The second line opens the proof, and says it will proceed
by the rule of conditional proof, which is abbreviated as @{term "impI"}, for ``implication 
introduction''. The third line opens the assumption @{term "A"}, the fourth line uses this assumption
to show @{term "A"}, and the fifth line says that proof is finished. *}

text {* There are two things about the proof that aren't quite so obvious. First, the word @{text "then"}
at the beginning of the fourth line says that this step in the proof follows from the previous line.
Second, the period at the end of the fourth line says, roughly, that this line reiterates, or is an
instance of, something already assumed or proved -- in this case the assumption in the previous line. *}

text {* Here is another simple example: *}

lemma positive_paradox: "A \<longrightarrow> B \<longrightarrow> A"
proof (rule impI)
  assume "A"
  show "B \<longrightarrow> A"
  proof (rule impI)
    assume "B"
    from `A` show "A".
  qed
qed

text {* This proof is also very simple, but there's a few more things to note.*}

text {* First, there are no brackets in the statement of the lemma. This is because there is 
convention that conditionals ``associate to the right''. In other words, the lemma translates back
into English as ``if @{text "A"} then if  @{text "B"} then  @{text "A"}'', as opposed to ``if if
 @{text "A"} then @{text "B"} then @{text "A"}''.*}

text {* Second, just as in the last proof, this proof assumes the antecedent @{term "A"} and shows
the consequent @{term "B \<longrightarrow> A"}. But this time the consequent does not just reiterate something
already given, but itself has to proved. So the fifth line opens a new subproof within the proof. 
This subproof is closed in the eighth line, and the proof as a whole closed in the ninth. *}

text {* Third, on the seventh line  @{term "A"} does not follow from the assumption just before on
the sixth line, but from the much earlier assumption on the third line. So instead of using @{text "then"}
to refer to the previous line, we use @{text "from \<open>A\<close>"} to refer all the way back to the assumption
on the third line. *}

text {* Fourth, if you look closely at the proof you will notice that the assumption @{term "B"} on
the sixth line is not used to show anything at all -- @{term "A"} is doing all the work. This is quite
normal in classical natural deduction systems, but it's avoided in, for example, relevant logics,
which take issue with the fact that @{term "B"} is ``irrelevant'' in this proof.\footnote{For relevant
logics, see especially Anderson and Belnap @{cite "anderson_entailment_1976"}.} The logic automated 
by Isabelle is, of course, \emph{classical} logic. *}

text {* This point is important because it is not obvious that the lemma is true. Suppose, for example,
that @{term "A"} translates ``I will die young'' and @{term "B"} translates ``I will live healthily''. 
Then the lemma as a whole translates ``If I will die young, then I will die young even if I live
healthily'' But if my unhealthy lifestyle is the cause of my death, this is intuitively false. *}

text {* The example illustrates that classical logic is not philosophically neutral, even in some of its 
simplest manifestations. That means that not everything ``proved'' here -- no matter how reliable
the software or rigorous the proofs -- is incontrovertibly true. Whether the reasoning below is right
depends on whether classical logic is right. Nothing -- person or machine -- can guarantee that for
certain. *}

text {* The example also illustrates that results must be interpreted with care. The example sounds
in English as if it supports a fatalistic conclusion -- that my dying young is outside of my control.
But classically, the sentence is equivalent to ``if I will die young, then either I will not live
healthily or I will die young'' which, while true, has no fatalistic consequences. *}

text {* Finally, note that the lemma has been given a name, viz. @{term "positive_paradox"}. This is
helpful if we wish to refer back to the lemma in a later proof. It also reminds us about the significance
of the lemma -- in this case that it is one of the notorious ``paradoxes of material implication'',
for the reasons just mentioned. *}

text {* \begin{Exercise}[title={The Strict Positive Paradox}]
Practice using conditional proof by proving: \end{Exercise} *}

lemma strict_positive_paradox: "A \<longrightarrow> B \<longrightarrow> B" oops

(* Note the conditional is written by two dashes "--" followed by a greater than sign ">". *)

text {* Where would a proponent of relevant logic find fault with this proof? Think of an example
to show it's not obvious that this lemma is true. This problem is known as the \emph{strict} positive
paradox of material implication, since it's consequent @{term "B \<longrightarrow> B"} is a necessary truth. *}

text {* Note that the command @{text "oops"} allows you to state a lemma without proving it. Delete 
it before you start your proof. If you need to use a lemma that you haven't proved in another proof, you can
write @{text "sorry"} instead of @{text "oops"}. This command should obviously be used with care,
since a lemma merely derived from an unproved lemma is itself unproved. *}

subsubsection {* Modus Ponens *}

text {* According to the \emph{elimination} rule for conditionals, normally called modus ponens,
from a conditional and its antecedent you can show its consequent. Here is a simple example:  *}

lemma "A \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> B"
proof (rule impI)
  assume "A"
  show "(A \<longrightarrow> B) \<longrightarrow> B"
  proof (rule impI)
    assume "A \<longrightarrow> B"
    thus "B" using `A` by (rule mp)
  qed
qed

text {* The important part of this proof is the step from the sixth to seventh line, which uses
modus ponens to derive @{term "B"} from @{term "A \<longrightarrow> B"} using @{term "B"}. The rest of the proof
works by two applications of conditional proof, as just described in subsection \ref{conditional_proof}.
The only nuance is that @{text "then show"} is now abbreviated @{text "thus"}, which is purely for
the sake of brevity. *}

text {* Here is a slightly more complicated example: *}

lemma contraction: "(A \<longrightarrow> A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> B)"
proof (rule impI)
  assume "A \<longrightarrow> A \<longrightarrow> B"
  show "A \<longrightarrow> B"
  proof (rule impI)
    assume "A"
    with `A \<longrightarrow> A \<longrightarrow> B` have "A \<longrightarrow> B" by (rule mp)
    thus "B" using `A` by (rule mp)
  qed
qed

text {* Three things are notable about this proof. First, on line seven we said that we @{text "have"}
 @{term "A \<longrightarrow> B"} instead of that we @{text "show"} it. This is just to reflect that @{term "A \<longrightarrow> B"}
is not our final goal of this subproof -- it's just an intermediate step on our way to @{term "B"}
which we reach only on the eight line. In general, @{term "show"} and @{term "thus"} will appear only
on the last line of a proof or subproof. *}

text {* Second, order matters -- modus ponens works by deriving the consequent from the conditional 
followed by the antecedent, not from the antecedent followed by the conditional. To see what I mean,
consider the following variation of the same proof: *}

lemma "(A \<longrightarrow> A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> B)"
proof (rule impI)
  assume "A \<longrightarrow> A \<longrightarrow> B"
  show "A \<longrightarrow> B"
  proof (rule impI)
    assume "A"
    then have "A \<longrightarrow> B" using `A \<longrightarrow> A \<longrightarrow> B` by (rule rev_mp)
    thus "B" using `A` by (rule mp)
  qed
qed

text {* Everything is almost the same, except on the seventh line, where the order is switched and
@{text "with"} is replaced by @{text "then"} and @{text "using"} and @{term "mp"} is replaced by @{term "rev_mp"}.
This is annoying, because we don't normally care which order we have the antecedent and conditional
in when we apply modus ponens. But it doesn't matter, because you get used to it. *}

text {* \begin{Exercise} Practice conditional proof and modus ponens by proving: \end{Exercise} *}

lemma prefixing: "(A \<longrightarrow> B) \<longrightarrow> (C \<longrightarrow> A) \<longrightarrow> (C \<longrightarrow> B)" oops

lemma suffixing: "(A \<longrightarrow> B) \<longrightarrow> (B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)" oops

text {* Would a relevant logician logician find these proofs acceptable? What about the proof of
contraction above? *}

subsubsection {* Biconditional Introduction *}

text {* The introduction rule for a biconditional is just like the introduction rule for a
conditional, except as well as assuming the left hand side and proving the right hand side, one
must also assume the right hand side and prove the left hand side. Here is a very simple example: *}

lemma "A \<longleftrightarrow> A"
proof (rule iffI)
  assume "A"
  thus "A".
next
  assume "A"
  thus "A".
qed

text {* Note that in order to prove a biconditional, one must prove two things: the right side from 
the left side, and the left side from the right side. The word @{text "next"} in the middle of the
proof is just to signal the move from solving the first goal to solving the second. *}

subsubsection {* Biconditional Elimination: *}

text {* There are two elimination rules for biconditionals. The first is the same as modus ponens --
from a biconditional and it's left hand side, one can infer it's right hand side. For example: *}

lemma "(A \<longleftrightarrow> B) \<longrightarrow> A \<longrightarrow> B"
proof
  assume "A \<longleftrightarrow> B"
  show "A \<longrightarrow> B"
  proof
    assume "A"
    with `A \<longleftrightarrow> B` show "B" by (rule iffD1)
  qed
qed

text {* The second is the reverse -- from a biconditional and it's right hand side, one can infer
it's left hand side. For example: *}

lemma "(A \<longleftrightarrow> B) \<longrightarrow> B \<longrightarrow> A"
proof
  assume "A \<longleftrightarrow> B"
  show "B \<longrightarrow> A"
  proof
    assume "B"
    with `A \<longleftrightarrow> B` show "A" by (rule iffD2)
  qed
qed

text {* Notice that both these proofs work by conditional proof, but I've omitted to say so. If you
open a new subproof without specifying a rule, Isabelle will default to using the introduction rule
for the main connective of what you are trying to prove. This helps to keep proofs tidy, and focus
attention on the steps that matter most. *}

text {* \begin{Exercise}[label = biconditional] 
Practice biconditional elimination and introduction by proving: \end{Exercise} *}

lemma "(A \<longleftrightarrow> B) \<longleftrightarrow> (B \<longleftrightarrow> A)" oops

subsection {* Conjunction *}

(* Conjunction can be writing by typing "\and" using forward slash "/" followed by back slash "\" *)

text {* Conjunctions are translated with a wedge. So ``it's raining and it's cloudy'', for example,
is translated @{term "A \<and> B"}, where @{term "A"} stands for ``it's raining'' and @{term "B"} stands
for ``it's cloudy''. The next two subsections explain the introduction and elimination rules for
conjunctions. *}

subsubsection {* Conjunction Elimination *}

text {* According to the rule of conjunction elimination, from a conjunction, you can show each
conjunct. For example, from @{term "A \<and> B"} you can show @{term "A"}:  *}

lemma "A \<and> B \<longrightarrow> A"
proof
  assume "A \<and> B"
  thus "A" by (rule conjE)
qed

text {* And from @{term "A \<and> B"} you can also show @{term "B"}:  *}

lemma "A \<and> B \<longrightarrow> B"
proof
  assume "A \<and> B"
  thus "B" by (rule conjE)
qed

text {* Here is a more interesting example: *}

lemma import: "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<and> B \<longrightarrow> C)"
proof
  assume "A \<longrightarrow> B \<longrightarrow> C"
  show "A \<and> B \<longrightarrow> C"
  proof
    assume "A \<and> B"
    then have "A" by (rule conjE)
    with `A \<longrightarrow> B \<longrightarrow> C` have "B \<longrightarrow> C"..
    from `A \<and> B` have "B" by (rule conjE)
    with `B \<longrightarrow> C` show "C"..
  qed
qed

text {* Two things are notable about this proof. First, modus ponens or conditional elimination is
used twice in this proof. But this has been abbreviated by two dots instead. This abbreviation can
be used with all the basic introduction and elimination rules, for brevity. *}

text {* Second, there are no brackets around @{term "A \<and> B"} in the statement of the lemma. This is
because there is a convention that conjunction has higher priority than implication. That means we
do need brackets around @{term "A \<longrightarrow> B"} in the following example: *}

lemma "A \<and> (A \<longrightarrow> B) \<longrightarrow> B"
proof
  assume "A \<and> (A \<longrightarrow> B)"
  then have "A \<longrightarrow> B" by (rule conjE)
  from `A \<and> (A \<longrightarrow> B)` have "A" by (rule conjE)
  with `A \<longrightarrow> B` show "B"..
qed

text {* Notice that in both these proof we had to use conjunction elimination twice -- once for each
conjunct. This is of course a common pattern. *}

text {*  \begin{Exercise}[title = Strengthening the Antecedent] Practice conjunction elimination by proving: \end{Exercise} *}

lemma strengthening_the_antecedent: "(A \<longrightarrow> C) \<longrightarrow> (A \<and> B \<longrightarrow> C)" oops

text {* Thinks of an example to show it's not obvious that this lemma is true. Would a relevant logician
find fault with this proof? This lemma is known as ``strengthening the antecedent'', since @{term "A \<and> B"}
is stronger than, or in other words entails, @{term "A"}. *}

subsubsection {* Conjunction Introduction *}

text {* According to the rule for conjunction introduction, from the first and second conjuncts, you
can show the conjunction. Here is a very simple example: *}

lemma conjunction_commutative: "A \<and> B \<longrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  hence "B"..
  from `A \<and> B` have "A"..
  with `B` show "B \<and> A" by (rule conjI)
qed

text {* Note that @{text "hence"} in this proof abbreviates @{text "then have"}, just as @{text "thus"}
abbreviates @{text "then show"}, again for the sake of brevity. *}

text {* Here is a more interesting example: *}

lemma export: "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B \<longrightarrow> C)"
proof
  assume antecedent: "A \<and> B \<longrightarrow> C"
  show "A \<longrightarrow> B \<longrightarrow> C"
  proof
    assume "A"
    show "B \<longrightarrow> C"
    proof
      assume "B"
      with `A` have "A \<and> B" by (rule conjI)
      with antecedent show "C"..
    qed
  qed
qed

text {* Note how in this proof we have named the opening assumption ``antecedent'' so we can refer
back to it by name in the final step, instead of quoting the whole line. This becomes very useful in
the presentation of more complex proofs. Not also that, as with modus pones, order matters for
conjunction introduction. *}

text {* Like conditionals, conjunctions ``associate to the right''. This means that the associativity
of conjunction has to be proved: *}

lemma conjunction_associative: "A \<and> B \<and> C \<longleftrightarrow> (A \<and> B) \<and> C" 
proof
  assume left: "A \<and> B \<and> C"
  hence "A"..
  from left have "B \<and> C"..
  hence "B"..
  with `A` have "A \<and> B"..
  from `B \<and> C` have "C"..
  with `A \<and> B` show "(A \<and> B) \<and> C"..
next
  assume right: "(A \<and> B) \<and> C"
  hence "A \<and> B"..
  hence "B"..
  from right have "C"..
  with `B` have "B \<and> C"..
  from `A \<and> B` have "A"..
  thus "A \<and> B \<and> C" using `B \<and> C`..
qed

text {* Notice that in the left to right direction of this proof, @{term "A \<and> B"} couldn't be derived
from @{term "A \<and> B \<and> C"} in a single step -- @{term "A"} and @{term "B"} had to be derived separately
first. This is because the conjunction associates to the right, and so @{term "A \<and> B"} is not a conjunct
of @{term "A \<and> B \<and> C"} at all -- its conjuncts are just @{term "A"} and @{term "B \<and> C"}. *}
  
text {* \begin{Exercise} Practice conjunction introduction by proving: \end{Exercise}  *}

lemma "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> C) \<longrightarrow> A \<longrightarrow> B \<and> C" oops

subsection {* Disjunction *}

text {* Disjunctions are translated with a vee. So ``it's raining or it's cloudy'' is translated
@{term "A \<or> B"}, where @{term "A"} stands for ``it's raining'' and @{term "B"} stands for ``'it's cloudy''.
Needless to say, disjunction is \emph{inclusive}, so ``it's raining or it's cloudy'' is compatible with
``it's raining and it's cloudy''. The next two subsections explain the introduction and elimination
rules for disjunction. *}

subsubsection {* Disjunction Introduction *}

text {* There are two rules for disjunction introduction. According to the first, you can show a 
disjunction from its first disjunct. For example: *}

lemma "A \<longrightarrow> A \<or> B"
proof
  assume "A"
  thus "A \<or> B" by (rule disjI1)
qed

text {* According to the second, you can show a disjunction from its second disjunct. For example: *}

lemma "B \<longrightarrow> A \<or> B"
proof
  assume "B"
  thus "A \<or> B" by (rule disjI2)
qed

text {* Note that we can omit brackets around the disjunction, since it has higher priority than
implication. However, conjunction has higher priority than disjunction. *}

text {* \begin{Exercise} Practice disjunction introduction by proving: \end{Exercise} *}

lemma "(A \<longrightarrow> B) \<longrightarrow> (A \<longrightarrow> B \<or> C)" oops

subsubsection {* Disjunction Elimination *}

text {* Disjunction elimination is a bit more complicated. According to it, if you have a disjunction,
and you can prove something from both its disjuncts, then you can prove that thing simpliciter.
Here is a simple example: *}

lemma "A \<or> A \<longrightarrow> A"
proof
  assume "A \<or> A"
  thus "A"
  proof (rule disjE)
    assume "A"
    thus "A".
  next
    assume "A"
    thus "A".
  qed
qed

text {* Note the use of ``thus'' on the fourth line of this proof. To use disjunction elimination,
you need to show three things -- the disjunction itself, that the conclusion follows from the first
disjunct, and that the conclusion follows from the second disjunct. In this case, we already had the
disjunction, so we wrote ``thus'' in order to use it. But we could equally well have written the
proof in this slightly longer way: *}

lemma "A \<or> A \<longrightarrow> A"
proof
  assume "A \<or> A"
  show "A"
  proof (rule disjE)
    show "A \<or> A" using `A \<or> A`.
  next
    assume "A"
    thus "A".
  next
    assume "A"
    thus "A".
  qed
qed

text {* Note also that disjunction elimination is the key rule in our motivating example from
section \ref{propositional} -- I will be killed in the air raid or I will not, but \emph{either way}
taking precautions is pointless, so taking precautions is pointless. *}

text {* Like conditionals and conjunctions, disjunctions associate to the right.  *}

text {* \begin{Exercise} Practice disjunction elimination by proving: \end{Exercise} *}

lemma "(A \<longrightarrow> C) \<and> (B \<longrightarrow> C) \<longrightarrow> A \<or> B \<longrightarrow> C" oops

text {*  \begin{Exercise}[title = The Associativity of Disjunction] 
Prove the associativity of disjunction: \end{Exercise} *}

lemma "A \<or> B \<or> C \<longleftrightarrow> (A \<or> B) \<or> C" oops

text {* \begin{Exercise}[label = disjEexercises] Practice disjunction elimination and introduction by proving: \end{Exercise} *}

lemma "A \<or> B \<and> C \<longrightarrow> (A \<or> B) \<and> (A \<or> C)" oops

text {* Can you prove the converse from the rules covered so far? Why or why not? *}

subsection {* Negation *}

text {* Negation is translated by @{text "\<not>"}, so ``it's not raining'' is translated @{term "\<not> A"},
where @{term "A"} stands for ``it's raining''. Like the other connectives, negation has an introduction
rule and an elimination rule. We also discuss two other rules in this section -- classical contradiction,
which distinguishes classical from intuitionistic logic, and proof by cases. *}

subsubsection {* Negation Elimination *}

text {* According to the rule for negation elimination, if one has a negation, and also what it
negates, then one can derive anything at all. Here is a simple example: *}

lemma negative_paradox: "\<not> A \<longrightarrow> A \<longrightarrow> B"
proof
  assume "\<not> A"
  show "A \<longrightarrow> B"
  proof
    assume "A"
    with `\<not> A` show B by (rule notE)
  qed
qed

text {* Notice that @{term "B"} in this proof is completely arbitrary, and could have been any
proposition at all. *}

text {* This point is philosophically important, because it is not obvious that the lemma is true.
Suppose, for example, that @{term "A"} translates ``I live healthily'' and @{term "B"} translates ``I
will die young''. Then the lemma as a whole translates as ``If I do not live healthily, then I will
die young even if I live healthily''. But if my unhealthily lifestyle is the cause of my death,
this is intuitively false. *}

text {* The example is clearly closely related to the positive paradox of material implication from
section \ref{conditional_proof}, and for this reason it is known as the \emph{negative} paradox of
material implication. For this reason, both the lemma and the rule that supports it are rejected by
relevant logicians (even though there is no unused assumption here).\footnote{See Anderson and Belnap
@{cite "anderson_entailment_1976"} pp. 163-7.}
This is worth remembering, since otherwise the negative paradox is often a source of surprise. *}

text {* \begin{Exercise}[label = explosion] Prove that a contradiction entails anything: \end{Exercise} *}

lemma explosion: "A \<and> \<not> A \<longrightarrow> B" oops

text {* \begin{Exercise} Suppose the butler did it or the gardener did it. Then prove that if the butler didn't do it, 
the gardener did: \end{Exercise} *}

lemma "A \<or> B \<longrightarrow> \<not> A \<longrightarrow> B" oops

text {* How is the proof of this lemma related to the paradoxes of material implication. Would a
relevant logician accept it? *}

subsubsection {* Negation Introduction *}

text {* According to the rule for negation introduction if you assume something, and then you show
@{term "False"}, then you can show the negation of what you assumed. Here is an example, sometimes
known as the law of non-contradiction:  *}

lemma "\<not> (A \<and> \<not> A)"
proof (rule notI)
  assume "A \<and> \<not>A"
  hence " \<not> A"..
  moreover from `A \<and> \<not> A` have "A"..
  ultimately show "False" by (rule notE)
qed

text {* Two things are notable about this proof. First @{term "False"} doesn't have any introduction
rule of its own -- it's shown using by negation elimination, which as we emphasised in the previous
subsection can be used to show \emph{anything} from a contradiction. *}

text {* Second, @{term "False"} was shown from two facts -- @{term "\<not> A"} and @{term "A"}. So as to avoid
having to refer back to the first of these by name, we used the command @{text "moreover"} followed by
the command @{text "ultimately"}.  *}

text {* \begin{Exercise}[label = doublenegationintroduction] 
Practice negation introduction by proving: \end{Exercise} *}

lemma "A \<longrightarrow> \<not> \<not> A" oops

text {* \begin{Exercise}\label{doubleexcludedmiddle} The next example is challenging, but instructive. Prove: \end{Exercise} *}

lemma "\<not> \<not> (A \<or> \<not> A)" oops

text {* Hint: Assume @{term "\<not> (A \<or> \<not> A)"} and then prove @{term "A \<or> \<not> A"} by disjunction introduction
from  @{term "\<not> A"}. Can you prove simply @{term "A \<or> \<not> A"} from the rules covered so far. Why or 
why not? *}

subsubsection {* Classical Contradiction *}

text {* The rules we have learnt so far constitute the propositional fragment of \emph{intuitionistic}
logic. To get the full strength of classical logic, we need the rule of classical contradiction,
according to which if you can show @{term "False"} from a negation, then you can show what it negates.
Here is the simplest example:  *}

lemma "(\<not> A \<longrightarrow> False) \<longrightarrow> A"
proof
  assume "\<not> A \<longrightarrow> False"
  show "A"
  proof (rule ccontr)
    assume "\<not> A"
    with `\<not> A \<longrightarrow> False` show "False"..
  qed
qed

text {* And here is a proof of double negation elimination *}

lemma double_negation_elimination: "\<not>\<not>A \<longrightarrow> A"
proof
  assume "\<not>\<not>A"
  show "A"
  proof (rule ccontr)
    assume "\<not> A"
    with `\<not>\<not>A` show "False"..
  qed
qed

text {* Note that in many presentations of natural deduction, double negation elimination is the basic
rule and it is classical contradiction which is derived. *}

text {* \begin{Exercise}[title = The Law of Excluded Middle]\label{excludedmiddle} 
Prove the law of excluded middle: \end{Exercise} *}

lemma excluded_middle: "A \<or> \<not> A" oops

text {* How is this proof related to the proof in exercise \ref{doubleexcludedmiddle}, and to double negation elimination? *}

subsubsection {* Proof by Cases *}

text {* Proof by cases is really the application of disjunction elimination using the law of excluded
middle -- but since this is such a common pattern, it helps to have an abbreviation. As a simple example,
we use it to give another (circular) proof of the law of excluded middle itself:  *}

lemma "A \<or> \<not> A"
proof cases
  assume "A"
  thus "A \<or> \<not> A"..
next
  assume "\<not> A"
  thus "A \<or> \<not> A"..
qed

text {* \begin{Exercise}[title = Conditional Excluded Middle] Prove the Law of Conditional Excluded
Middle: \end{Exercise} *}

lemma "(A \<longrightarrow> B) \<or> (A \<longrightarrow> \<not> B)" oops

text {* How is the proof related to the positive paradox? Can you think of an intuitive counterexample? *}

text {* \begin{Exercise} Prove: \end{Exercise} *}

lemma "(A \<longrightarrow> B) \<or> (B \<longrightarrow> A)" oops

text {* Think of an example to show it's not obvious that this lemma is true. How is the proof of
the lemma related to the paradoxes of material implication? *}

text {*  \begin{Exercise}  Prove the converse from Exercise \ref{disjEexercises}: \end{Exercise} *}

lemma "(A \<or> B) \<and> (A \<or> C) \<longrightarrow> A \<or> B \<and> C" oops

  text {*  \begin{Exercise}[title = The Equivalence Thesis]
The theory of conditionals encapsulated in the classical natural deduction rules can be
summed up by the equivalence thesis, according to which a conditional is true if and only if
its antecedent is false or its consequent is true. So prove:  \end{Exercise} *}

lemma "(A \<longrightarrow> B) \<longleftrightarrow> (\<not> A \<or> B)" oops

text {* Equivalently, a conditional is true if and only if it's not the case that it's antecedent is
true and it's consequent is false. So prove: *}

lemma "(A \<longrightarrow> B) \<longleftrightarrow> \<not> (A \<and> \<not> B)" oops

text {* Where would a proponent of relevant logic fault these proofs? *}

text {* \begin{Exercise}[title = The Air Raid] The motivating argument from section \ref{propositional} could be formalised like this: \end{Exercise} *}

lemma
  assumes "A \<or> \<not> A"
  assumes "A \<longrightarrow> B \<longrightarrow> A"
  assumes "(B \<longrightarrow> A) \<longrightarrow> D"
  assumes "\<not> A \<longrightarrow> C \<longrightarrow> \<not> A"
  assumes "(C \<longrightarrow> \<not> A) \<longrightarrow> D"
  shows "D" oops

text {* Note that premises can be written with @{text "assumes"} and the conclusion with @{text "shows"}.
Which of the premises can be proven in classical logic? Where could an intuitionist logician object to
the argument. Where could a relevant logician object? And where must a classical logician, who accepts
the equivalence thesis but rejects fatalism, object? *}

section {* Predicate Logic *}

text {* Just as the natural deduction system for propositional logic has an introduction and elimination 
rule for each connective, the natural deduction system for first-order predicate logic has introduction and elimination
rules for each quantifier, and for identity. *}

subsection {* Universal Quantification  *}

text {* The universal quantifier is translated with an upside down ``A''. So ``all men are mortal'',
for example, is translated as @{term "\<forall> x. F x \<longrightarrow> G x"} where @{term "F x"} stands for ``is a man''
and @{term "F x"} for ``is mortal''. The next two subsections explain the introduction and elimination
rules for the universal quantifier. *}

subsubsection {* Universal Elimination *}

text {* If you have a universal statement, then you can replace the variable it binds with any term 
(of the same type). For example, if everything is an @{term "F"} then @{term "a"} is an @{term "F"}: *}

lemma "(\<forall> x. F x) \<longrightarrow> F a"
proof
  assume "\<forall> x. F x"
  thus "F a" by (rule allE)
qed

text {* Two things are notable about this example. The first is that the conventions for brackets are 
slightly different from usual -- the scope of the quantifier is everything within the surrounding 
brackets. The second is that there has to be a space between the predicate and name or variable,
to make sure they are different terms (the advantage of this is that terms don't have to be a single
letter or character, and so you don't have to worry about running out). *}

text {* \begin{Exercise} Practice universal elimination by proving: \end{Exercise} *}

lemma "(\<forall> x. F x) \<longrightarrow> F a \<and> F b" oops

text {* \begin{Exercise}[title = The Riddle of Dracula, label = dracula]
Prove that if everyone is afraid of Dracula, then if Dracula is afraid only of me, then I am Dracula: \end{Exercise} *}

lemma "(\<forall> x. R x d) \<longrightarrow> (\<forall> z. R d z \<longrightarrow> z = m) \<longrightarrow> d = m" oops

text {* Why is this lemma surprising?\footnote{This example is from Richard Cartwright, reported by
Smullyan @{cite "smullyan_what_1978"} p. 212.}  *}

subsubsection {* Universal Introduction *}

text {* To introduce a universally quantified statement, once must first prove an instance for an
arbitrary term. Here is a very simple example: *}

lemma "\<forall> x. F x \<longrightarrow> F x"
proof (rule allI)
  fix a
  show "F a \<longrightarrow> F a"
  proof
    assume "F a"
    thus "F a".
  qed
qed

text {* The role of @{text "fix"} in the third line is to introduce an arbitrary term. I've used the
term @{term "a"}, as one might in an introductory logic textbook, but of course any new term would do 
-- a popular choice in this case would just be @{term "x"}. *}

text {* \begin{Exercise} Practice universal elimination and introduction by proving: \end{Exercise} *}

lemma "(\<forall> x. F x \<and> G x) \<longrightarrow> (\<forall> x. F x)" oops

text {* \begin{Exercise} Prove that if everyone is at the party, then everyone in the world is at the party: \end{Exercise} *} 

lemma "(\<forall> x. F x) \<longrightarrow> (\<forall> x. F x \<longrightarrow> G x)" oops
  
text {* How is this lemma related to the positive paradox?  *}

subsection {* Existential Quantification *}

text {* The existential quantifier is translated with a backward ``E''. So `some man is mortal', for
example, is translated @{term "\<exists> x. F x \<and> G x"} where @{term "F x"} stands for `is a man'
and @{term "F x"} stands for `is mortal'. The next two subsections explain the introduction and
elimination rules for the existential quantifier. *}

subsubsection {* Existential Introduction *}

text {* According to the rule of existential introduction, from some term satisfying a sentence,
one can show that something satisfies that sentence. For example: *}

lemma "F a \<longrightarrow> (\<exists> x. F x)"
proof
  assume "F a"
  thus "\<exists> x. F x" by (rule exI)
qed

text {* Here is a trickier example: *}

lemma "\<exists> x. \<not> F x \<or> F x"
proof -
  from excluded_middle have "\<not> F a \<or> F a".
  thus "\<exists> x. \<not> F x \<or> F x" by (rule exI)
qed

text {* Notice that there is a ``@{text "-"}'' just after @{text "proof"}. This is to stop Isabelle from
defaulting to applying the existential introduction immediately, as she normally would. If she did, then
she would expect you to show @{term "\<not> F a \<or> F a"} for some \emph{old} name @{term "a"}. But you don't
have any old name, and so you'd be stuck. Instead, you have to prove @{term "\<not> F a \<or> F a"} first, and
then apply existential introduction afterwards -- now to an old name. *}

text {* \begin{Exercise}[title = The Converse Drinkers Principle, label = conversedrinker]
Prove that there is someone such that if anyone drinks, then they do: \end{Exercise} *}

lemma "\<exists> x. (\<exists> y. F y) \<longrightarrow> F x" oops

text {* How is this proof related to the paradoxes of material implication?\footnote{This problem is
from Smullyan @{cite "smullyan_what_1978"} p. 210-1. It is the converse of exercise \ref{drinker}.}  *}

text {* \begin{Exercise}[label = demorgan] Prove that if not everything is @{term "F"}, something is not @{term "F"}: \end{Exercise} *}

lemma not_all_implies_some_not: "\<not> (\<forall> x. F x) \<longrightarrow> (\<exists> x. \<not> F x)" oops

text {* Would an intuitionist accept this proof? *}

text{* \begin{Exercise} Prove that if everything is @{term "F"}, then something is @{term "F"}: \end{Exercise} *}

lemma "(\<forall> x. F x) \<longrightarrow> (\<exists> x. F x)" oops

subsubsection {* Existential Elimination *}

text {* According to the rule of existential elimination, if something satisfies a sentence, then
you can obtain a name for that thing. For example: *}

lemma "(\<exists> x. F x \<and> G x) \<longrightarrow> (\<exists> x. F x)"
proof
  assume "\<exists> x. F x \<and> G x"
  then obtain a where "F a \<and> G a" by (rule exE)
  hence "F a"..
  thus "\<exists> x. F x"..
qed

text {* Note that you can use any letter for the introduced term, but the computer can tell if you
try to cheat. For example, you cannot prove:  *}

lemma "(\<exists> x. F x) \<longrightarrow> F a" oops 

text {* Since although you can use existential elimination to obtain @{term "F a"}, your computer
will not accept that as resolving your goal, since it knows that the ``new'' name you introduced is
not the same as the ``old'' name you had in your goal (try it and you'll see what I mean). *}

text {* \begin{Exercise} Practice existential introduction and elimination by proving: \end{Exercise} *}

lemma "(\<exists> x. F x) \<longrightarrow> (\<exists> x. F x \<or> G x)" oops

text {* \begin{Exercise}[title = {The Drinker Principle}, label = drinker] 
Prove that there is someone such that if they drink, then everybody drinks: \end{Exercise} *}

lemma "\<exists> x. F x \<longrightarrow> (\<forall> x. F x)" oops

text {* How is this theorem related to the paradoxes of material implication?\footnote{This problem
is from Smullyan @{cite "smullyan_what_1978"}, pp. 209-11. It's a common example in automated theorem
proving. See, for example, Barendregt @{cite "barendregt_quest_1996"}, pp. 54-55.}  *}

subsection {* Identity *}

text {* The identity predicate is translated by the familiar sign @{text "="}. So `Hesperus is Phosphorus',
for example, is translated as @{term "a = b"}. *}

subsubsection {* Reflexivity *}

text {* According to the introduction rule for identity, one may show at anytime that something is
identical to itself. For example, we can prove that everything is self-identical: *}

lemma "\<forall> x. x = x"
proof
  fix a
  show "a = a " by (rule refl)
qed

text {* \begin{Exercise} Practice the reflexivity rule by proving: \end{Exercise} *}

lemma "F a \<longrightarrow> a = a" oops

text {* \begin{Exercise}[label = everythingissomething] Prove that everything is identical to something: \end{Exercise} *}

lemma "\<forall> x. \<exists> y. x = y" oops

subsubsection {* Substitution *}

text {* According to the rule of substitution, if you have  @{term "x = y"} and you have @{term "A"},
then you can substitute @{term "y"} for occurrences of @{term "x"} in @{term "A"}. For example:  *}

lemma "a = b \<longrightarrow> F a \<longrightarrow> F b"
proof
  assume "a = b"
  show "F a \<longrightarrow> F b"
  proof
    assume "F a"
    with `a = b` show "F b" by (rule subst)
  qed
qed

text {* Notice that this rule only allows you to use @{term "a = b"} to substitute @{term "a"} for
@{term "b"}, and not vice versa. However, the following variation of the rule is available: *}

lemma "a = b \<longrightarrow> F b \<longrightarrow> F a"
proof
  assume "a = b"
  show "F b \<longrightarrow> F a"
  proof
    assume "F b"
    with `a = b` show "F a" by (rule ssubst)
  qed
qed

text {* The difference is subtle -- just one extra `s' at the beginning of the rule.  *}

text {* \begin{Exercise}[label = symmetry] Prove the symmetry of identity: \end{Exercise} *}

lemma "a = b \<longrightarrow> b = a" oops

text {* \begin{Exercise} Prove the transitivity of identity: \end{Exercise}  *}

lemma "a = b \<longrightarrow> b = c \<longrightarrow> a = c" oops

text {* \begin{Exercise}[title = The Indiscernibility of Identity] Prove the indiscernibility of identicals: \end{Exercise} *}

lemma "x = y \<longrightarrow> (F x \<longleftrightarrow> F y)" oops

subsection {* Definite Descriptions *}

text {* According to the introduction rule for definite descriptions, to show that something is
the @{term "F"} one may first show two things. First, that it is an @{term "F"}. Second that any
arbitrary @{term "F"} is that thing. For example:  *}

lemma "(THE x. x = a) = a"
proof (rule the_equality)
  show "a = a"..
next
  fix b
  assume "b = a"
  thus "b = a".
qed

text {* Note that one cannot eliminate definite descriptions in the way one might expect. For example,
neither of the following can be proved: *}

lemma "G (THE x. F x) \<longrightarrow> (\<exists> x. F x)" oops
lemma "F (THE x. F x) \<longrightarrow> (\<exists> x. \<forall> y. F y \<longrightarrow> y = x)" oops

text {* The advantage of this is that definite descriptions function just like any other term. For
example the following is valid: *}

lemma "(\<forall> x. F x) \<longrightarrow> F (THE x. G x)"
proof
  assume "\<forall> x. F x"
  thus "F (THE x. G x)" by (rule allE)
qed

text {* This is not in accordance with the traditional Russellian theory, so this is something that
has to be kept in mind, especially since many philosophers do assume the Russellian analysis.\footnote{
For Russell's theory of definite descriptions see @{cite "russell_denoting_1905"}.} *}

text {* \begin{Exercise} Practice introducing definite descriptions by proving: \end{Exercise} *}

lemma "(\<forall> x. F x \<longleftrightarrow> x = a) \<longrightarrow> (THE x. F x) = a" oops

section {* Automation *}

text {* By now you probably feel more like the slave from Liebniz' quotation than an excellent person.
But happily, Isabelle contains many automated tools to make your work easier. I will describe three of
the most useful. *}

subsection {* Nitpick *}

text {* Nitpick is a counterexample generator.\footnote{See Blanchette and Nipkow @{cite "blanchette_nitpick_2010"}.} 
For example, to generate a counterexample to the fallacy of affirming the consequent, you could type: *}

lemma 
  assumes "p \<longrightarrow> q"
  assumes "q"
  shows "p" nitpick oops

text {* In which case nitpick will inform you of a countermodel in which  @{term "p"} is false and 
@{term "q"} is true. *}

subsection {* Sledgehammer *}

text {* Sledgehammer looks for a proof using various automated theorem provers.\footnote{See Blanchette
and Paulson @{cite "blanchette_hammering_2016"}.} 
Here is an example:  *}

lemma "(\<forall> x. F x \<longrightarrow> G x) \<or> (\<exists> x. F x \<and> \<not> G x)" sledgehammer
  by auto

text {* To produce an explicit natural deduction style proof, you can try: *}

lemma "(\<forall> x. F x \<longrightarrow> G x) \<or> (\<exists> x. F x \<and> \<not> G x)" sledgehammer [isar_proofs]
proof -
{ assume "\<not> F v0_0 \<or> G v0_0"
  have ?thesis
      by blast }
  then show ?thesis
    by blast
qed

text {* Unsurprisingly, the result is not quite so legible as a hand written proof. *}

subsection {* Try *}

text {* What if you don't know whether the statement you're interested in is a theorem? Try try: *}

lemma "(\<forall> x. \<exists> y. R x y) \<longrightarrow> (\<exists> y. \<forall> x. R x y)" try oops

lemma "(\<exists> x. \<forall> y. R x y) \<longrightarrow> (\<forall> y. \<exists> x. R x y)" try
  by auto

(*<*) end (*>*)