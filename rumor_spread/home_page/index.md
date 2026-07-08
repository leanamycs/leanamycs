---
# Feel free to add content and custom Front Matter to this file.
# To modify the layout, see https://jekyllrb.com/docs/themes/#overriding-theme-defaults

# layout: home
usemathjax: true
---

A complete (`sorry`-free) Lean 4 + Mathlib formalization of the classical
rumor-spreading result in distributed computing: in the uniform *push*
model on the complete graph $K_n$, if one node is informed initially, then
after $O(\log n)$ rounds all nodes are informed with high probability. The
main theorem is `RumorPush.push_informs_all_whp`.

Useful links:

* [Source repository](https://github.com/Aakash-verse/Rumor_Spreading_on_Kn)
* [Blueprint]({{ site.url }}/blueprint/)
* [Blueprint as pdf]({{ site.url }}/blueprint.pdf)
* [Dependency graph]({{ site.url }}/blueprint/dep_graph_document.html)
* [Doc pages for this repository]({{ site.url }}/docs/)
* [Zulip chat for Lean](https://leanprover.zulipchat.com/) for coordination