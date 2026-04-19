
**⚠️ Precise for simple graphs; gap remains for general graphs.** The
predecessor-distance consistency clause is a meaningful strengthening that,
combined with the existing reachability and completeness clauses, makes the
spec precise for the tested 3-vertex chain (where paths are unique). However,
on graphs with multiple shortest paths, the spec still does not include an
explicit shortest-path optimality clause of the form
`∀w,k. reachable_in(w,k) ⟹ dist[w] ≤ k`. The HEAD report acknowledges
this: "Shortest-path follows from unique paths; general graphs need optimality
clause." I rate this as **✅ Precise for tested cases, with a theoretical gap
on multi-path graphs** — the gap is minor since the BFS tree structure
(`dist[v] = dist[pred[v]] + 1`) combined with reachability already constrains
distances tightly.