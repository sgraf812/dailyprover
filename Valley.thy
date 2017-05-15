text \<open>https://coq-math-problems.github.io/Problem1/\<close>

theory Valley 
  imports Main
begin
  
inductive valley_at :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool"
  where valley_at_0: "valley_at f x 0"
  | extend_valley: "\<lbrakk>valley_at f x n; f x = f (x + n + 1)\<rbrakk> \<Longrightarrow> valley_at f x (Suc n)"
   
lemma valley_def: "valley_at f x n \<longleftrightarrow> (\<forall>y. x \<le> y \<and> y \<le> x + n \<longrightarrow> f x = f y)"
proof (intro iffI)
  assume "valley_at f x n"
  thus "\<forall>y. x \<le> y \<and> y \<le> x + n \<longrightarrow> f x = f y"
    by (induction rule: valley_at.induct) (auto elim: le_SucE)
next
  assume "\<forall>y. x \<le> y \<and> y \<le> x + n \<longrightarrow> f x = f y"
  thus "valley_at f x n"
    by (induction n) (auto intro: valley_at_0 extend_valley)
qed
    
abbreviation "decr" where "decr f \<equiv> monotone op \<le> op \<ge> f"
    
lemma valley_or_drop: "decr f \<Longrightarrow> valley_at f x n \<or> (\<exists>y. f y < f x)"
  by (metis nat_less_le valley_def monotone_def)

lemma 
  assumes "decr f" 
  shows "\<exists>x. valley_at f x n"
proof (induction arbitrary: n rule: measure_induct_rule[of f])
  case (less x)
  with \<open>decr f\<close> valley_or_drop show ?case
    by blast
qed
  
end