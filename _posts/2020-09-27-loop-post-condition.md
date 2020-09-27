---
title: "Schematic construction of loop post-condition"
---

To demonstrate ideas behind a mechanical finding of loop post-condition, we consider the inner loop of function `strlen`:
{% highlight C %}
while (a[i] != '\0') { i++ };
{% endhighlight %}
Assuming that $$R$$ is the post-condition, we first formally write the weakest precondition $$Q(i) = wp(S(i), R)$$ for this `while` loop, denoted as $$S(i)$$ here. That gives us the loop invariant and, finally, its post-condition $$R$$.

<!--more-->

The first step on this way is to find recurrent relationships. In the simplest case, like ours, it could be made with a single step of loop unrolling:
{% highlight C %}
if (a[i] != '\0') {
  i++;
  while (a[i] != '\0') { i++ };
}
{% endhighlight %}
Thanks to formalized Hoare rules, we get the weakest-precondition for conditionals

$$Q(i) = (A(i) \Rightarrow wp(\mathtt{i{+}{+}}; S(i), R)) \land (\lnot A(i) \Rightarrow wp(\mathtt{skip}, R))$$

where condition `a[i] != '\0'` inside the if-clause is denoted as $$A(i)$$. There are two obvious simplifications:

$$wp(\mathtt{i{+}{+}}; S(i), R) = wp(\mathtt{i{+}{+}}, Q(i)) = Q(i + 1)$$

and $$wp(\mathtt{skip}, R) = R$$; with the help of which the weakest precondition is written as

$$Q(i) = (A(i) \Rightarrow Q(i + 1)) \land (\lnot A(i) \Rightarrow R)$$

and further,

$$Q(i) = (\lnot A(i) \lor Q(i + 1)) \land (A(i) \lor R)$$

Here, we took into account that $$X \Rightarrow Y \equiv \lnot X \lor Y$$.

The loop invariant corresponds to the assumption that the loop never stops, i.e., $$R = \mathrm{false}$$. That gives us the desired recurrent relationships

$$Q(i) = A(i) \land Q(i + 1)$$

Note that function `strlen` initiates the `while` loop with `i = 0`; hence, our loop invariant reads

$$\forall i \geq 0: A(i)$$

The trick giving us the loop post-condition is to get the inverse of the loop invariant:

$$\exists i \geq 0: \lnot A(i)$$

Expanding proposition $$A(i)$$, one concludes that we should meet some $$i \geq 0$$, for which `a[i] == '\0'`.
