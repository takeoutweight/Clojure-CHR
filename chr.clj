(ns chr
  (:use [bench])
  (:require [clojure.set :as set]))

(def ^:dynamic *trace-set* #{})
(def ^:dynamic *trace-ignore* #{})
(defn trace
  ([labels strs]
     (trace labels strs (last strs)))
  ([labels strs expr]
     (when (and (not-empty (set/intersection (into #{:all} labels) *trace-set*))
                (empty? (set/intersection (into #{} labels) *trace-ignore*)))
       (print (last labels))
       (print ", ")
       (doall (for [s strs] (print s "")))
       (println)
       (flush))
     expr))

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
  (bench
   :rewrite
   (map (fn [t] (get rewrite-map t t)) pattern)))

(defn dissoc-constraint
  [store [term & rst]]
  (bench
   :dissoc-constraint
   (if (empty? rst)
     (set/difference store #{term})
     (let [b (dissoc-constraint (get store term) rst)]
       (if (empty? b)
         (dissoc store term)
         (assoc store term b))))))

(defn impose-constraint
  [store constraint]
  (bench
   :impose-constraint
   (update-in store (drop-last constraint) set/union #{(last constraint)})))

(defn unwrap
  "Returns the sequence of constraints comprised by a given store.
   Nested stores are not recursively unwrapped.
   assert: (= some-store (reduce impose-constraint {} (unwrap some-store)))"
  [store]
  (if (set? store)
    (map vector store)
    (mapcat (fn [[k v]] (map #(vec (concat [k] %)) (unwrap v))) store)))

(defn sort-guards
  "given a collection of variables that will be grounded, sorts into
   [grounded, ungrounded] guards--so you know which are possible to check."
  [guards grounded-variables]
  (bench
   :sort-guards
   (let [ground-set (into #{} grounded-variables)
         {ground true unground false}
         , (group-by (fn [[args gfn]] (every? #(or (not (variable? %))
                                                   (ground-set %)) args))
                     guards)]
     [ground unground])))

(defn find-matches
  "Returns a seq of substitution maps, arity of pattern must be matched."
  ([store guards pattern] (find-matches store {} guards pattern))
  ([store substs guards [term & next-terms]]     
     (bench
      :find-matches
      (let [term (get substs term term)]
        (cond
         (nil? next-terms) (if (set? store)
                             (if (variable? term)
                               (filter
                                #(every? (fn [[args gfn]] (apply gfn (rewrite args %))) guards)
                                (map #(assoc substs term %) store))
                               (if (get store term) [substs] []))
                             [])
         (set? store) ()
         (variable? term) (let [[grnd-guards ungrnd-guards] (sort-guards guards (conj (keys substs) term))]
                            (if (not (empty? grnd-guards))
                              (map first grnd-guards)
                              (map first ungrnd-guards))
                            (mapcat (fn [[k v]]
                                      (let [next-substs (assoc substs term k)]
                                        (if (every? (fn [[args gfn]]
                                                      (apply gfn (rewrite args next-substs)))
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
  (bench
   :match-head
   (if pattern
     (let [[grnd-guards ungrnd-guards] (sort-guards (partial-apply-guards guards substs) pattern)
           subbed-pat (rewrite pattern substs) 
           next-substs (find-matches store substs grnd-guards subbed-pat)]
       (trace [:match-head] ["Matched on " pattern "with subs" next-substs "with guards"(map first grnd-guards) ])
       (when (not (empty? next-substs))
         (mapcat (fn [sb]
                   (match-head (dissoc-constraint store (rewrite pattern sb))
                               sb ungrnd-guards rst)) next-substs)))
     [[substs store]])))

(defn matching-rule-seq
  "doesn't filter against propagation history.
   returns a seq of [fired-rule, subs, next-store] tuples."
  [store rules active-constraint]
  (for [rule rules
        [_op pattern] (:head rule) 
        [grnd-guards ungrnd-guards] [(sort-guards (:guards rule) pattern)]
        next-substs (find-matches (impose-constraint {} active-constraint) grnd-guards pattern)
        [sibling-substs s0] (trace [:awake :search]
                                   ["subs" next-substs
                                    "on pattern:" pattern
                                    "with grnd-guards" grnd-guards]
                                   (match-head store
                                               next-substs
                                               ungrnd-guards
                                               (filter #(not= pattern %)
                                                       (map second (:head rule)))))]
    [rule sibling-substs s0]))

(defn awake
  ([rules initial-constraints]
     (awake {} rules (first initial-constraints) (rest initial-constraints) #{} nil))
  ([store rules active-constraint queued-constraints prop-history next-rule-matches]
     (if active-constraint
       (let [t1 (System/currentTimeMillis)
             [[fired-rule substs next-store] & next-rule-matches]
             , (or next-rule-matches
                   (filter (fn [[rule substs _]] (or (not-empty (filter (fn [[op _]] (= op :remove)) (:head rule)))
                                                     (not (prop-history [rule substs]))))
                           (matching-rule-seq store rules active-constraint)))]
         (if (and (empty? (find-matches store [] active-constraint)) fired-rule) 
           (let [_ (bench-here :awake-found t1)
                 t2 (System/currentTimeMillis)
                 next-history (if (not-empty (filter (fn [[op _]] (= op :remove)) (:head fired-rule)))
                                prop-history
                                (trace [:awake] ["updating history to: " (into prop-history [[fired-rule substs]])]))
                 _ (trace [:awake] [(map (fn [[op pat]] [op (rewrite pat substs)]) (:head fired-rule))])
                 {kept-awake [:keep true],
                  kept-asleep [:keep false]}
                 ,  (group-by (fn [[op pat]] [op (= pat active-constraint)])
                              (map (fn [[op pat]] [op (rewrite pat substs)]) (:head fired-rule)))
                 [next-active & next-queued] (concat
                                              (concat (map #(rewrite % substs) (:body fired-rule))
                                                      (map second kept-awake)
                                                      (when-let [[args bfn] (:bodyfn fired-rule)]
                                                        (apply bfn (rewrite args substs))))
                                              queued-constraints)]
             (trace [:awake :firing] ["store:" (unwrap store) "with"
                                      (concat (map #(rewrite % substs) (:body fired-rule))
                                              (when-let [[args bfn] (:bodyfn fired-rule)]
                                                (apply bfn (rewrite args substs)))) "with subs:" substs])
             (bench-here (:name fired-rule) t2)
             #_"If no constraints to be removed, maintain same store and position within the iterator."
             (if (empty? (filter (fn [[op _]] (= op :remove)) (:head fired-rule)))
               (recur (reduce impose-constraint store (map second kept-asleep))
                      rules next-active next-queued next-history next-rule-matches)
               (recur (reduce impose-constraint next-store (map second kept-asleep))
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
  [args & body]
  `[~args (fn ~args ~@body)])


(def leq-rules (exists [x y z a b eq eq1 eq2 c d]
                       [{:name :Reflexivity
                         :head [[:remove [:leq d d]]]}
                        {:name :Transitivity
                         :head [[:keep [:leq x y]]
                                [:keep [:leq y z]]]
                         :body [[:leq x z]]}
                        
                        #_"Herbrand equality"
                        #_{:name :Eq-reflexivity
                         :head [[:remove [:equivclass d d]]]}
                        #_{:name :Eq-transitivity
                         :head [[:remove [:equivclass y x]]
                                [:keep [:equivclass eq y]]]
                         :body          [[:equivclass eq x]]}
                        #_{:name :Eq-simplification
                         :head [[:remove [:equivclass eq1 x]]
                                [:remove [:equivclass eq2 x]]]
                         :bodyfn (chrfn [x eq1 eq2] [[:equivclass (if (< (hash eq1) (hash eq2)) eq1 eq2) x]])}
                        {:name :Eq-rewrite1
                         :head [[:remove [:leq x b]]
                                [:keep [:equivclass eq x]]]
                         :body [[:leq eq b]]}
                        {:name :Eq-rewrite2
                         :head [[:remove [:leq b x]]
                                [:keep [:equivclass eq x]]]
                         :body [[:leq b eq]]}
                        
                        
                        {:name :Antisymmetry
                         :head [[:remove [:leq x y]]
                                [:remove [:leq y x]]]
                         :bodyfn (chrfn [x y] (if (< (hash x) (hash y))
                                                [[:equivclass x y]]
                                                [[:equivclass y x]]))}
                        ]))

;fails on 4?
;infinite loops w/ reflexivity.
;loops with BOTH leq worlds. (one is OK)
(defn solve-leq-chain
  "all variables equal on x1 <= x2 <= ... xn <= x1"
  [length]
  (unwrap (awake leq-rules (map (fn [[l u]] [:leq l u])
                                (conj (map vector (range (dec length)) (drop 1 (range)))
                                      [(dec length) 0])))))


(def gcd-rules (exists [n m]
                       [{:head [[:remove [:gcd 0]]]}
                        {:head [[:keep [:gcd n]]
                                [:remove [:gcd m]]]
                         :guards [(chrfn [m n] (>= m n))]
                         :bodyfn (chrfn [m n] [[:gcd (- m n)]])}]))

(defn find-gcd [n1 n2]
  (unwrap (awake gcd-rules [[:gcd n1] [:gcd n2]])))
