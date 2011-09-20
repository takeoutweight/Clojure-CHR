(ns chr
  (:use [chr.debug])
  (:require [clojure.set :as set]
            [clojure.walk :as walk]))

(defn variable? [x]
  (::variable (meta x)))

(defn variable
  "No effort expended to make variables hygenic.
   Scope ranges over entire rules (head & body)."
  [x]
  (with-meta x {::variable true}))

(defmacro exists
  [varlist & body]
  `(let [~@(mapcat (fn [v] [v `(variable (quote ~v))]) varlist)]
     ~@body))

(defn rewrite
  [pattern rewrite-map]
  (no-bench
   :rewrite
   (map (fn [t] (get rewrite-map t t)) pattern)))

(defn dissoc-constraint
  [store [term & rst]]
  (no-bench
   :dissoc-constraint
   (if (empty? rst)
     (set/difference store #{term})
     (let [b (dissoc-constraint (get store term) rst)]
       (if (empty? b)
         (dissoc store term)
         (assoc store term b))))))

(defn impose-constraint
  [store constraint]
  (no-bench
   :impose-constraint
   (update-in store (drop-last constraint) set/union #{(last constraint)})))

(defn sort-guards
  "given a collection of variables that will be grounded, sorts into
   [grounded, ungrounded] guards--so you know which are possible to check."
  [guards grounded-variables]
  (no-bench
   :sort-guards
   (let [ground-set (into #{} grounded-variables)
         {ground true unground false}
         , (group-by (fn [[args gfn]] (every? #(or (not (variable? %))
                                                   (ground-set %)) args))
                     guards)]
     [ground unground])))

(defn unwrap
  "Returns the sequence of constraints comprised by a given store.
   Nested stores are not recursively unwrapped.
   assert: (= some-store (reduce impose-constraint {} (unwrap some-store)))"
  [store]
  (if (set? store)
    (map vector store)
    (mapcat (fn [[k v]] (map #(vec (concat [k] %)) (unwrap v))) store)))

(defn find-matches
  "Returns a seq of substitution maps, arity of pattern must be matched."
  ([store pattern] (find-matches store {} [] pattern))
  ([store guards pattern] (find-matches store {} guards pattern))
  ([store substs guards [term & next-terms]]     
     (no-bench
      :find-matches
      (let [term (get substs term term)]
        (cond
         (nil? next-terms) (if (set? store)
                             (if (variable? term)
                               (filter
                                #(every? (fn [[args gfn]] (apply gfn store (rewrite args %))) guards)
                                (map #(assoc substs term %) store))
                               (if (get store term) [substs] []))
                             [])
         (= ::& term) (let [rest (first next-terms) 
                            [grnd-guards _] (sort-guards guards (conj (keys substs) rest))]
                        (filter
                         (fn [next-subs] (every? (fn [[args gfn]]
                                                   (apply gfn store (rewrite args next-subs)))
                                                 grnd-guards))
                         (map #(assoc substs rest %) (unwrap store))))
         (set? store) (if (= (first next-terms) ::&)
                        (let [rest (second next-terms)]
                          (if (variable? term)
                            (filter
                             #(every? (fn [[args gfn]] (apply gfn store (rewrite args %))) guards)
                             (map #(assoc substs term % rest []) store))
                            (if (get store term) [(assoc substs rest [])] [])))
                        ())
         (variable? term) (let [[grnd-guards ungrnd-guards] (sort-guards guards (conj (keys substs) term))]
                            (mapcat (fn [[k v]]
                                      (let [next-substs (assoc substs term k)]
                                        (if (every? (fn [[args gfn]]
                                                      (apply gfn store (rewrite args next-substs)))
                                                    grnd-guards)
                                          (find-matches v
                                                        next-substs
                                                        ungrnd-guards
                                                        next-terms)
                                          [])))
                                    store))
         (vector? term) (let [[grnd-guards ungrnd-guards] (sort-guards guards (concat (keys substs) term))]
                          (mapcat (fn [[k v]]
                                    (mapcat (fn [submatch]
                                              (find-matches v (merge substs submatch) ungrnd-guards next-terms))
                                            (find-matches k substs grnd-guards term)))
                                  (filter (fn [[k v]] (map? k)) store)))
         :else (find-matches (get store term) substs  guards next-terms))))))

(defn partial-apply-guards
  "takes a collection of guards, and grounds their
   argument templates according to the substitution."
  [guards substs]
  (map (fn [[args gfn]] [(rewrite args substs) gfn]) guards))

(defn match-head
  "list of all viable [subststitutions, store-after-removal]
   pairs that match this collection of patterns"
  [store substs guards [pattern & rst]]
  (if pattern
    (let [[grnd-guards ungrnd-guards] (bench :mh-sort-guards (sort-guards (partial-apply-guards guards substs) pattern))
          subbed-pat (bench :mh-rewrite (rewrite pattern substs)) 
          next-substs (bench :mh-find-matches (find-matches store substs grnd-guards subbed-pat))]
      (trace [:match-head] ["Matched on " pattern "with subs" next-substs "with guards"(map first grnd-guards) ])
      (mapcat (fn [sb] (match-head (bench :mh-dissoc (dissoc-constraint store (rewrite pattern sb)))
                                   sb ungrnd-guards rst))
              next-substs))
    [[substs store]]))

(defn matching-rule-seq
  "doesn't filter against propagation history.
   returns a seq of [fired-rule, subs, next-store] tuples."
  [store rules active-constraint]
  (for [rule rules
        [_op pattern] (:head rule)
        :let [[grnd-guards ungrnd-guards] (bench :sort-guards
                                                 (sort-guards (:guards rule) pattern))]
        next-substs (bench :find-matches
                           (find-matches (impose-constraint {} active-constraint) grnd-guards pattern))
        [sibling-substs s0] (trace [:awake :search]
                                   ["subs" next-substs
                                    "on pattern:" pattern
                                    "with grnd-guards" grnd-guards]
                                   (bench :match-head
                                          (match-head store
                                                      next-substs
                                                      ungrnd-guards
                                                      (filter #(not= pattern %)
                                                              (map second (:head rule))))))]
    [rule sibling-substs s0]))

(defn fire-rule
  [fired-rule substs store]
  (concat (map #(rewrite % substs) (:body fired-rule))
          (when-let [[args bfn] (:bodyfn fired-rule)]
            (apply bfn store (rewrite args substs)))))

(def kill (atom 5))

(defn awake
  ([rules initial-constraints]
     (awake {} rules (first initial-constraints) (rest initial-constraints) #{} nil))
  ([rules store initial-constraints]
     (awake store rules (first initial-constraints) (rest initial-constraints) #{} nil))
  ([store rules active-constraint queued-constraints prop-history continued-rule-matches]
     (if (and active-constraint (>= (swap! kill dec) 0))
       (let [t1 (System/nanoTime)
             [[fired-rule substs next-store new-constraints] & next-rule-matches]
             , (filter
                (fn [[fired-rule substs next-store new-constraints]]
                  (let [matched (into #{} (map (fn [[_op pat]] (rewrite pat substs)) (:head fired-rule)))
                        new (into #{} new-constraints)]
                    (not= matched new))
                  #_(not (prop-history [fired-rule substs new-constraints])))
                (map (fn [[fired-rule substs next-store]]
                       [fired-rule substs next-store (fire-rule fired-rule substs next-store)])
                     (or continued-rule-matches
                         (matching-rule-seq store rules active-constraint))))]
         (if (and (empty? (bench :find-matches (find-matches store [] active-constraint)))
                  fired-rule) 
           (let [_ (bench-here :awake-found t1)
                 t2 (System/nanoTime)                 
                 _ (trace [:awake] [(map (fn [[op pat]] [op (rewrite pat substs)]) (:head fired-rule))])                 
                 next-history (into prop-history [[fired-rule substs new-constraints]])
                 {kept-awake-group [:+ true],
                  kept-asleep-group [:+ false]}
                 ,  (group-by (fn [[op pat]] [op (= pat active-constraint)])
                              (map (fn [[op pat]] [op (rewrite pat substs)]) (:head fired-rule)))
                 kept-awake (map second kept-awake-group)
                 kept-asleep (map second kept-asleep-group)
                 [next-active & next-queued] (concat new-constraints
                                                     kept-awake
                                                     queued-constraints)]
             (trace [:awake :firing] [(:name fired-rule) "on store:" (unwrap store)"::"active-constraint"::" queued-constraints
                                      "kept-awake:" kept-awake "kept-asleep:" kept-asleep "creating" new-constraints "with subs:" substs])
             (bench-here (:name fired-rule) t2)
             #_"If no constraints to be removed, maintain same store and position within the iterator."
             (if (empty? (filter (fn [[op _]] (= op :-)) (:head fired-rule)))
               (recur store
                      rules active-constraint (doall (concat new-constraints queued-constraints)) next-history (or next-rule-matches [])) ;must distinguish between empty and nil, nil means don't use, empty means none left-
               (recur (reduce impose-constraint next-store kept-asleep)
                      rules next-active next-queued next-history nil)))
           (do
             (bench-here :awake-fail t1)
             (recur (impose-constraint store active-constraint)
                    rules
                    (first queued-constraints)
                    (rest queued-constraints)
                    prop-history
                    nil))))
       store)))

(defmacro chrfn
  "chrfns must be of the form
   (chrfn [store arg1 ...argn]) where store is
   the current state of the constraint store"
  [args & body]
  `[~(vec (drop 1 args)) (fn ~args ~@body)])

(defmacro rule
  ([head body] 
     `(rule ~(symbol (str "rule-" (mod (hash [head body]) 10000))) ~head ~body))
  ([name head body]
     (let [occurrences (vec (map (fn [[op pat]] [op (walk/postwalk
                                                     (fn [t] (get {'& ::&
                                                                   '_ (variable (gensym "_"))} t t))
                                                     pat)])
                                 (filter (fn [[op pat]] (#{:- :+} op)) (partition 2 head))))
           guards (vec (map second (filter (fn [[op pat]] (= :when  op)) (partition 2 head))))
           store-alias (or (last (map second (filter (fn [[op pat]] (= :store op)) (partition 2 head))))
                           'store)
           variables (into #{} (for [pattern (map second occurrences)
                                     term pattern
                                     :when (symbol? term)] term))
           collect-vars (fn [form] (walk/postwalk (fn [f] (cond (variables f) #{f}
                                                                (coll? f) (apply set/union f)
                                                                :else nil)) form))]
       `(exists ~(vec variables)
                {:name (quote ~name)
                 :head ~occurrences
                 :guards [~@(map (fn [g] `(chrfn [~store-alias ~@(collect-vars g)] ~g)) guards)]
                 :bodyfn (chrfn [~store-alias ~@(collect-vars body)] ~body)}))))

;---------------- Examples ---------------------

(def leq-rules (exists [x y z a b eq eq1 eq2 c d]
                       [{:name :Reflexivity
                         :head [[:- [:leq d d]]]}
                        
                        {:name :Antisymmetry
                         :head [[:- [:leq x y]]
                                [:- [:leq y x]]]
                         :bodyfn (chrfn [_ x y] (if (< (hash x) (hash y))
                                                  [[:equivclass x y]]
                                                  [[:equivclass y x]]))}

                        #_"Herbrand equality:"       
                        {:name :Eq-rewrite1
                         :head [[:- [:leq x b]]
                                [:+ [:equivclass eq x]]]
                         :body [[:leq eq b]]}
                        {:name :Eq-rewrite2
                         :head [[:- [:leq b x]]
                                [:+ [:equivclass eq x]]]
                         :body [[:leq b eq]]}
                        {:name :Eq-reflexivity
                         :head [[:- [:equivclass d d]]]}
                        {:name :Eq-transitivity
                         :head [[:- [:equivclass y x]]
                                [:+ [:equivclass eq y]]]
                         :body          [[:equivclass eq x]]}
                        {:name :Eq-simplification
                         :head [[:- [:equivclass eq1 x]]
                                [:- [:equivclass eq2 x]]]
                         :bodyfn (chrfn [_ x eq1 eq2] [[:equivclass (if (< (hash eq1) (hash eq2)) eq1 eq2) x]])}

                        {:name :Transitivity
                         :head [[:+ [:leq x y]]
                                [:+ [:leq y z]]]
                         :body [[:leq x z]]}]))

(defn solve-leq-chain
  "all variables equal on x1 <= x2 <= ... xn <= x1"
  [length]
  (awake leq-rules (map (fn [[l u]] [:leq l u])
                        (conj (map vector (range (dec length)) (drop 1 (range)))
                              [(dec length) 0]))))


(def gcd-rules (exists [n m]
                       [{:head [[:- [:gcd 0]]]}
                        {:head [[:+ [:gcd n]]
                                [:- [:gcd m]]]
                         :guards [(chrfn [_ m n] (>= m n))]
                         :bodyfn (chrfn [_ m n] [[:gcd (- m n)]])}]))

(defn find-gcd [n1 n2]
  (unwrap (awake gcd-rules [[:gcd n1] [:gcd n2]])))
