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
    (is (has-edge? g edgeid))
    (is (has-edge? g [:n1 :in] [:n2 :out]))

    (is (=msets #{::pg/edge001} (edges g)))

    (set-attr [:n2 :out] [:n1 :in] :weight 1.0)
    (is (= 1.0 (attr g edgeid :weight)))
    (is (= 1.0 (attr g [:n1 :in] [:n2 :out] :weight)))
    (is {:weight 1.0} (user-attrs g edgeid))
    (is {:weight 1.0} (user-attrs g [:n1 :in] [:n2 :out]))
    (is {::pg/elem-type ::pg/edge
         ::pg/id ::pg/edge001
         ::pg/incident-ports #{[:n2 :out] [:n1 :in]}
         :weight 1.0})

    (set-attrs :n1 {:x 1 :y 2})
    (is (= {:x 1 :y 2} (user-attrs g :n1)))

    (set-attrs [:n1 :in] [:n2 :out] {:w 2.0 :x 3.0})
    (is (= {:w 2.0 :x 3.0} (user-attrs g [:n1 :in] [:n2 :out])))

    (rm-attr [:n1 :in] [:n2 :out] :w)
    (is (not (has-attr? g edgeid :w)))
    (rm-attr edgeid :x)
    (is (not (has-attr? g [:n1 :in] [:n2 :out] :x)))))

#_(deftest test-neighbors
  (with-state [g (pgraph :n1 :n2 :n3)]
    (add-edge [:n1 :out] [:n2 :in])
    (add-edge [:n2 :out] [:n3 :in])
    (bind e1 (find-edgeid g [:n1 :out] [:n2 :in]))
    (bind e2 (find-edgeid g [:n2 :out] [:n3 :in]))
    (is (=sets [e1 e2] (edges g)))

    (is (has-edge? g e1))
    (is (not (has-edge? g :n1)))
    (is (not (has-edge? g :not-defined)))

    (is (=msets [e1] (elem->incident-edges g :n1)))
    (is (=msets [e1 e2] (elem->incident-edges g :n2)))

  ))
