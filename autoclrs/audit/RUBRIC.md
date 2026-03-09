Every algorithm or data structure should be formalized in the following structure:

* CLRS.ChXX.AlgoName.Spec.fst
    - Pure F* specification of the algorithm

* CLRS.ChXX.AlgoName.Lemmas.fst
    - Proofs of lemmas about the pure specification, e.g., optimiality results,
      correctness properties of the spec etc.

* CLRS.ChXX.AlgoName.Lemmas.fsti
    - Interface file with signatures of the lemmas

* CLRS.ChXX.AlgoName.Complexity.fst
    - Proofs of the associated math lemmas about complexity properties, if any,
      about the algorithm

* CLRS.ChXX.AlgoName.Complexity.fsti
    - Interface file with signatures of the complexity lemmas and any associated
      definitions

* CLRS.ChXX.AlgoName.Impl.fst
    - Implementation of the algorithm in Pulse, proven to be functionally
      equivalent to the specification as defined in AlgoName.Spec.fst

* CLRS.ChXX.AlgoName.Impl.fsti
    - Main public signature for the imperative implementation
