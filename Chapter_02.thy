theory Exercises_Chapter_02
imports Main
begin

section "Exercise 2.1"

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"
  
section "Exercise 2.2"

(* datatype nat = Zero | Suc nat *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n"
| "add (Suc m) n = Suc (add m n)"

theorem add_assoc [simp]: "add (add xs ys) zs = add xs (add ys zs)"
  apply(induction xs)
  apply(auto)
  done

lemma add_zero [simp]: "add xs 0 = xs"
  apply(induction xs)
  apply(auto)
  done

lemma add_suc [simp]: "add x (Suc y) = Suc (add x y)"
  apply(induction x)
  apply(auto)
  done

theorem add_comm [simp]: "add xs ys = add ys xs"
  apply(induction xs)
  apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0"
| "double n = add n n"

theorem double_two_adds [simp]: "double m = add m m"
  apply(induction m)
  apply(auto)
  done

section "Exercise 2.3"

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0"
| "count x (y # xs) = (if x = y then Suc(count x xs) else count x xs)"

theorem count_less_than_length [simp]: "(count x xs) \<le> (length xs)"
  apply(induction xs)
  apply(auto)
  done

value "count (1::int) [(1::int), (2::int), (3::int), (1::int)]"

section "Exercise 2.4"

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] y = [y]"
| "snoc (x # xs) y =  x # (snoc xs y)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []"
| "reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp]: "reverse (snoc xs x) = x # reverse xs"
  apply(induction xs)
  apply(auto)
  done

theorem reverse_cancels [simp]: "reverse(reverse(xs)) = xs"
  apply(induction xs)
  apply(auto)
  done

section "Exercise 2.5"

fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"
| "sum_upto n = n + sum_upto(n-1)"

theorem sum_formula [simp]: "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
  apply(auto)
  done

end