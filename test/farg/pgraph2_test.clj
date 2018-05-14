(ns farg.pgraph2-test
  (:refer-clojure :exclude [rand rand-int cond])
  (:require [better-cond.core :refer [cond]]
            [clojure.tools.trace :refer [deftrace] :as trace]
            [clojure.pprint :refer [pprint]]
            [clojure.test :refer :all]
            [com.rpl.specter :as S]
            [farg.pgraph2 :as pg :refer :all :exclude [pprint]]
            [farg.util :as util :refer [dd dde =msets]]
            [farg.with-state :refer [with-state]]))

(deftest test-basics
  (with-state [g (pgraph)]
    (is (=msets #{} (nodes g)))
    (is (not (has-node? g :n1)))
    (is (not (has-elem? g :n1)))

    (add-node :n1)
    (is (has-node? g :n1))
    (is (has-elem? g :n1))
    (is (not (has-edge? g :n1)))

    (add-node :n2 {:a 52})
    (is (has-node? g :n2))
    (is (=msets #{:n1 :n2} (nodes g)))
    (is (= 52 (attr g :n2 :a)))
    (is (= nil (attr g :n1 :a)))
    (is (= {:a 52, ::pg/elem-type ::pg/node, ::pg/id :n2} (attrs g :n2)))
    (is (= {:a 52} (user-attrs g :n2)))

    (set-attr :n1 :b 522)
    (is (= 522 (attr g :n1 :b)))

    (rm-attr :n1 :b)
    (is (nil? (attr g :n1 :b)))
    (is (not (has-attr? g :n1 :b)))

    (set-attr :n1 :b nil)
    (is (nil? (attr g :n1 :b)))
    (is (has-attr? g :n1 :b))

    (update-attr :n2 :a inc)
    (is (= 53 (attr g :n2 :a)))

    (update-attr :n2 :a + 2 3)
    (is (= 58 (attr g :n2 :a)))

    (is (not (has-edge? g [:n1 :in] [:n2 :out])))
    (add-edge nil [:n1 :in] [:n2 :out])
    (bind edgeid (find-edgeid g [:n1 :in] [:n2 :out]))
    (is (= ::pg/edge001 edgeid))
  ))
