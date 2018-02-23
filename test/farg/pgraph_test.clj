(ns farg.pgraph-test
  (:refer-clojure :exclude [rand rand-int cond])
  (:require [better-cond.core :refer [cond]]
            [clojure.tools.trace :refer [deftrace] :as trace]
            [clojure.pprint :refer [pprint]]
            [clojure.test :refer :all]
            [farg.pgraph :as pg :refer :all]
            [farg.util :as util :refer [dd dde]]
            [farg.with-state :refer [with-state]]))

(deftest test-basics
  (with-state [g (pgraph)]
    (add-node :n1)
    (is (has-node? g :n1))
    (is (not (has-node? g :n2)))
    (add-node :n2 {:a 52})
    (is (has-node? g :n2))
    (is (= 52 (attr g :n2 :a)))
    ;(is (= {} (attrs g :n1)))
    ;(is (= {:a 52} (attrs g :n2)))
    (is (not (has-edge? g [:n1 :in] [:n2 :out])))
    (add-edge [:n1 :in] [:n2 :out])
    (bind edgeid (find-edgeid g [:n1 :in] [:n2 :out]))
    (is (= ::pg/edge001 edgeid))
    (is (has-edge? g edgeid))
    (is (has-edge? g [:n1 :in] [:n2 :out]))
    ))
