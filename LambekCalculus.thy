theory LambekCalculus
  imports Main
begin

datatype 'a category =
  Atomic 'a ("^")
  | LeftFunctional "'a category" "'a category" (infix "←" 65)
  | RightFunctional "'a category" "'a category" (infix "→" 65)

inductive Lambek :: "'a category list ⇒ 'a category ⇒ bool" (infix "⊢" 60)
  where
  identity : "[x]⊢x"
  | cut : "⟦A@[x]@B⊢y; C⊢x⟧ ⟹ A@C@B⊢y"
  | left_intro_1 : "⟦A@[x]@B⊢y; C⊢z⟧ ⟹ A@C@[z→x]@B⊢y"
  | left_intro_2 : "⟦A@[x]@B⊢y; C⊢z⟧ ⟹ A@[x←z]@C@B⊢y"
  | right_intro_1 : "A@[x]⊢y ⟹ A⊢x→y"
  | right_intro_2 : "[x]@A⊢y ⟹ A⊢y←x"

lemma rev_right_intro_1:
  assumes "A⊢y←x"
    shows "A@[x]⊢y"
proof -
  have "[y←x]@[x]⊢y"
    by (metis append_Cons append_Nil identity left_intro_2)
  thus ?thesis
    by (metis append_Nil assms cut)
qed

lemma rev_right_intro_2:
  assumes "A⊢x→y"
    shows "[x]@A⊢y"
proof -
  have "[x]@[x→y]⊢y"
    by (metis append_Cons append_Nil identity left_intro_1)
  thus ?thesis
    by (metis append_Nil2 assms cut)
qed

theorem type_raising_1: "[x]⊢(y←x)→y"
  using
    rev_right_intro_1
    rev_right_intro_2
    right_intro_1
    identity by blast 

theorem type_raising_2: "[x]⊢y←(x→y)"
  using
    rev_right_intro_1
    rev_right_intro_2
    right_intro_2
    identity
  by blast 

inductive CPS :: "'a category ⇒ 'a category ⇒ 'a category ⇒ bool"
      and CPS' :: "'a category ⇒ 'a category ⇒ 'a category ⇒ bool"
  where
  "CPS' a x y ⟹ CPS a x ((a←y)→a)"
  | "CPS' a x y ⟹ CPS a x (a←(y→a))"
  | "⟦CPS' a x1 y1; CPS a x2 y2⟧ ⟹ CPS' a (x1→x2) (y1→y2)"
  | "⟦CPS' a x1 y1; CPS a x2 y2⟧ ⟹ CPS' a (x2←x1) (y2←y1)"
  | "CPS' a (^x) (^x)"

lemma CPS_and_CPS': "{y. CPS a x y} = ((λy. (a←y)→a) ` {y. CPS' a x y}) ∪ ((λy. a←(y→a)) ` {y. CPS' a x y})"
  apply auto
  apply (smt (verit, ccfv_SIG) CollectI CPS.simps image_iff) 
  apply (simp add: CPS_CPS'.intros(1)) 
  by (simp add: CPS_CPS'.intros(2))

theorem CPS_is_finite:
  fixes a x :: "'a category"
  shows "finite {y. CPS' a x y}"
    and "finite {y. CPS a x y}"
proof (induct x)
  case (Atomic x)
  case 1
  have "{y. CPS' a (^x) y} = {(^x)}"
    proof
      have "⋀y. CPS' a (^x) y ⟹ y=(^x)"
        by (metis category.distinct(1) category.distinct(3) CPS'.simps)
      thus "{y. CPS' a (^x) y} ⊆ {(^x)}" by auto
      have "CPS' a (^x) (^x)"
        by (simp add: CPS_CPS'.intros(5))
      thus "{(^x)} ⊆ {y. CPS' a (^x) y}" by auto
    qed
  thus ?case by auto
  case 2
    thus ?case by (simp add: ‹finite {b. CPS' a (^ x) b}› CPS_and_CPS') 
next
  case (LeftFunctional x1 x2)
  case 1
  have "finite ((λ(u, v). (u←v)) ` ({y. CPS a x1 y}×{y. CPS' a x2 y}))"
    using LeftFunctional.hyps(2) LeftFunctional.hyps(3) by blast
  moreover have "{y. CPS' a (x1←x2) y} = (λ(u, v). (u←v)) ` ({y. CPS a x1 y}×{y. CPS' a x2 y})"
    apply auto
    apply (smt (verit, best) CollectI SigmaI category.distinct(1) category.distinct(5) category.inject(2) CPS'.cases pair_imageI)
    by (simp add: CPS_CPS'.intros(4))
  ultimately show ?case
    by presburger
  case 2
  have "finite (((λy. (a←y)→a) ` {y. CPS' a (x1←x2) y}) ∪ ((λy. a←(y→a)) ` {y. CPS' a (x1←x2) y}))"
    using ‹finite {b. CPS' a (x1 ← x2) b}› by blast
  thus ?case by (simp add: CPS_and_CPS') 
next
  case (RightFunctional x1 x2)
  case 1
  have "finite ((λ(u, v). (u→v)) ` ({y. CPS' a x1 y}×{y. CPS a x2 y}))"
    using RightFunctional.hyps(1) RightFunctional.hyps(4) by blast
  moreover have "{y. CPS' a (x1→x2) y} = (λ(u, v). (u→v)) ` ({y. CPS' a x1 y}×{y. CPS a x2 y})"
    apply auto
    apply (smt (verit, ccfv_SIG) CollectI SigmaI category.distinct(3) category.distinct(5) category.inject(3) CPS'.cases pair_imageI) 
    by (simp add: CPS_CPS'.intros(3))
  ultimately show ?case by presburger 
  case 2 show ?case by (simp add: ‹finite {b. CPS' a (x1 → x2) b}› CPS_and_CPS') 
qed

inductive rCPS :: "'a category ⇒ 'a category ⇒ 'a category ⇒ bool"
      and rCPS' :: "'a category ⇒ 'a category ⇒ 'a category ⇒ bool"
  where
  "rCPS' a x y ⟹ rCPS a x ((a←y)→a)"
  | "rCPS' a x y ⟹ rCPS a x (a←(y→a))"
  | "rCPS a x2 y2 ⟹ rCPS' a ((^x1)→x2) ((^x1)→y2)"
  | "rCPS a x2 y2 ⟹ rCPS' a (x2←(^x1)) (y2←(^x1))"
  | "rCPS' a (^x) (^x)"

lemma CPS_contains_rCPS:
  fixes a x :: "'a category"
  shows "{y. rCPS' a x y} ⊆ {y. CPS' a x y}"
    and "{y. rCPS a x y} ⊆ {y. CPS a x y}"
proof (induct x)
  case (Atomic x)
  case 1 show ?case apply auto using CPS'.simps rCPS'.cases by fastforce 
  case 2 show ?case apply auto by (smt (verit, ccfv_threshold) ‹{b. rCPS' a (^ x) b} ⊆ {b. CPS' a (^ x) b}› rCPS.cases CPS_CPS'.intros(1) CPS_CPS'.intros(2) mem_Collect_eq subsetD) 
next
  case (LeftFunctional x1 x2)
  case 1 show ?case apply auto by (smt (verit, ccfv_SIG) Collect_mono_iff LeftFunctional.hyps(2) category.distinct(5) category.inject(2) CPS'.simps rCPS'.cases) 
  case 2 show ?case apply auto by (smt (verit, ccfv_SIG) Collect_mono_iff ‹{b. rCPS' a (x1 ← x2) b} ⊆ {b. CPS' a (x1 ← x2) b}› CPS.simps rCPS.cases) 
next
  case (RightFunctional x1 x2)
  case 1 show ?case apply auto by (smt (verit, ccfv_SIG) Collect_mono_iff RightFunctional.hyps(4) category.inject(3) category.simps(9) CPS'.simps rCPS'.cases) 
  case 2 show ?case apply auto by (smt (verit, ccfv_SIG) Collect_mono_iff ‹{b. rCPS' a (x1 → x2) b} ⊆ {b. CPS' a (x1 → x2) b}› CPS.simps rCPS.cases) 
qed

theorem rCPS_is_finite:
  shows "finite {y. rCPS' a x y}"
    and "finite {y. rCPS a x y}"
apply (meson CPS_contains_rCPS(1) CPS_is_finite(1) infinite_super)
by (meson CPS_contains_rCPS(2) CPS_is_finite(2) infinite_super)

theorem rCPS_transformation:
  fixes a x :: "'a category"
  shows "⋀y. rCPS' a x y ⟹ [x]⊢y"
    and "⋀y. rCPS a x y ⟹ [x]⊢y"
proof (induct x)
  case (Atomic x)
  {case 1
    show ?case using "1.prems" rCPS'.cases identity by blast}
  {case 2
    have "⋀y. rCPS' a (^x) y ⟹ [^x]⊢y"
      using "2.prems" rCPS'.cases identity by blast
    moreover hence "⋀y. rCPS' a (^x) y ⟹ [^x]⊢(a←y)→a"
      by (metis append_Cons append_Nil cut type_raising_1)
    moreover hence "⋀y. rCPS' a (^x) y ⟹ [^x]⊢a←(y→a)"
      by (metis category.distinct(1) category.distinct(3)
                rCPS'.cases type_raising_2)
    ultimately show "⋀y. rCPS a (^x) y ⟹ [^x]⊢y"
      by (metis rCPS.cases)}
next
  case (LeftFunctional x1 x2)
  hence "⋀y1. rCPS a x1 y1 ⟹ [x1←x2]@[x2]⊢y1"
    by (metis append.left_neutral append_Cons
              cut identity rev_right_intro_1)
  hence "⋀y1. rCPS a x1 y1 ⟹ [x1←x2]⊢y1←x2"
    using rev_right_intro_1 right_intro_2 by blast
  hence "⋀y1. rCPS' a (x1←x2) (y1←x2) ⟹ [x1←x2]⊢y1←x2"
    using rCPS'.cases by force
  thus "⋀y. rCPS' a (x1←x2) y ⟹ [x1←x2]⊢y"
    using rCPS'.cases by force
  hence "⋀y. rCPS' a (x1←x2) y ⟹ [x1←x2]⊢(a←y)→a ∧ [x1←x2]⊢a←(y→a)"
    by (metis append.left_neutral append_Cons
              cut type_raising_1 type_raising_2)
  thus "⋀y. rCPS a (x1←x2) y ⟹ [x1←x2]⊢y"
    by (metis rCPS.cases)
next
  case (RightFunctional x1 x2)
  hence "⋀y2. rCPS a x2 y2 ⟹ [x1]@[x1→x2]⊢y2"
    by (metis (no_types, hide_lams) append.left_neutral
              append_Nil2 cut rev_right_intro_1 type_raising_2)
  hence "⋀y2. rCPS a x2 y2 ⟹ [x1→x2]⊢x1→y2"
    using rev_right_intro_2 right_intro_1 by blast
  hence "⋀y2. rCPS' a (x1→x2) (x1→y2) ⟹ [x1→x2]⊢x1→y2"
    using rCPS'.cases by force
  thus "⋀y. rCPS' a (x1→x2) y ⟹ [x1→x2]⊢y"
    using rCPS'.cases by force
  hence "⋀y. rCPS' a (x1→x2) y ⟹ [x1→x2]⊢(a←y)→a ∧ [x1→x2]⊢a←(y→a)"
    by (metis append.left_neutral append_Cons
              cut type_raising_1 type_raising_2)
  thus "⋀y. rCPS a (x1→x2) y ⟹ [x1→x2]⊢y"
    by (metis rCPS.cases)
qed

lemma Type_raising_1_is_CPS : "rCPS a (^x) (a←((^x)→a))"
  and Type_raising_2_is_CPS : "rCPS a (^x) ((a←(^x))→a)"
apply (simp add: rCPS_rCPS'.intros(2) rCPS_rCPS'.intros(5))
  by (simp add: rCPS_rCPS'.intros(1) rCPS_rCPS'.intros(5))

end
