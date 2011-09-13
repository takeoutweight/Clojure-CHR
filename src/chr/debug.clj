(ns chr.debug
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

;comment out traces at the source level:
#_(defmacro trace
  ([labels strs] (last strs))
  ([labels strs expr] expr))

(def times (atom {}))

(defn reset-bench []
  (swap! times (fn [_] {})))

#_(defmacro bench
  [bench-key expression]
  `(let [start-time# (System/nanoTime)
         e# ~expression
         end-time# (System/nanoTime)]
     (swap! times update-in [~bench-key] (fn [[old-count# old-time#]]
                                           [(inc (or old-count# 0))
                                            (+ (or old-time# 0) (* (- end-time# start-time#)
                                                                   0.000001))]))
     e#))

(defmacro bench
  "commenting out all benchmark hooks at the sorce level."
  [bench-key expression] expression)

(defmacro no-bench
  "comment out specific benchmark hooks at the source level."
  [bench-key expression]
  expression)

(defn bench-here
  "add a benchmark time from the given start-time (in nanoseconds)"
  [bench-key start-time]
  (let [end-time (System/nanoTime)]
    (swap! times update-in [bench-key] (fn [[old-count old-time]]
                                         [(inc (or old-count 0))
                                          (+ (or old-time 0) (* (- end-time start-time)
                                                                0.000001))]))))
