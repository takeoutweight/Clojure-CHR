Quick little implementation of CHR in Clojure. Attempting to roughly follow CHR2 as described
in Peter Van Weert's dissertation [Extension and Optimising Compilation of Constraint Handling Rules](https://lirias.kuleuven.be/bitstream/123456789/266875/1/thesis.pdf)

Disclaimer:

Set semantics is currently baked in. Propagation history is opt-in. No "aggregates" semantics
yet. No optimizations to speak of.

_Not tested. Don't build bridges that depend on this code._


Use the RULE macro for CHR-like definitions:
--------------------------------------------

    (def narrowing-rules
         [(rule range-lower-bound
                [:- [:Range m1 M1]
                 :- [:Range m2 M2]
                 :when (number? m1)
                 :when (number? m2)]
                [[:Range (max m1 m2) M1]
                 [:Range (max m1 m2) M2]])
          (rule range-upper-bound
                [:- [:Range m1 M1]
                 :- [:Range m2 M2]
                 :when (number? M1)
                 :when (number? M2)]
                [[:Range m1 (min M1 M2)]
                 [:Range m2 (min M1 M2)]])
          (rule empty-range
                [:- [:Range m M]
                 :when (and (number? m)
                            (number? M)
                            (< M m))]
                [[:Error (str "Empty range: [" m "," M "]")]])])

    (unwrap (awake narrowing-rules [[:Range 30 90] [:Range 49 60] [:Range 'some-unground-var 59]]))

The RULE macro is just sugar; rules can be constructed directly:

    (def leq-rules (fresh [x y z]
                       [{:head [[:- [:leq x x]]]}
                        {:head [[:- [:leq x y]]
                                [:- [:leq y x]]]
                         :body [[:equals x y]]}
                        {:head [[:+ [:leq x y]]
                                [:+ [:leq y z]]]
                         :body [[:leq x z]]}]))

    (defn generate-leq-facts
      [pairs-o-symbols]
      (unwrap (awake leq-rules (map (fn [[l u]] [:leq l u]) pairs-o-symbols))))`


    (def gcd-rules (fresh [n m]
                       [{:head [[:- [:gcd 0]]]}
                        {:head [[:+ [:gcd n]]
                                [:- [:gcd m]]]
                         :guards [(chrfn [m n] (>= m n))]
                         :bodyfn (chrfn [m n] [[:gcd (- m n)]])}]))

    (defn find-gcd [n1 n2]
      (unwrap (awake gcd-rules [[:gcd n1] [:gcd n2]])))

