(ns farg.pgraph-test
  (:refer-clojure :exclude [rand rand-int cond])
  (:require [better-cond.core :refer [cond]]
            [clojure.tools.trace :refer [deftrace] :as trace]
            [clojure.pprint :refer [pprint]]
            [clojure.test :refer :all]
            [com.rpl.specter :as S]
            [farg.pgraph :as pg :refer :all :exclude [pprint]]
            [farg.util :as util :refer [dd dde]]
            [farg.with-state :refer [with-state]]))

(defn =sets [a b]
  (and (= (count a) (count b))
       (= (set a) (set b))))

(deftest test-basics
  (with-state [g (pgraph)]
    (is (=sets #{} (nodes g)))
    (is (not (has-node? g :n1)))
    (is (not (has-elem? g :n1)))

    (add-node :n1)
    (is (has-node? g :n1))
    (is (has-elem? g :n1))

    (add-node :n2 {:a 52})
    (is (has-node? g :n2))
    (is (=sets #{:n1 :n2} (nodes g)))
    (is (= 52 (attr g :n2 :a)))
    (is (= {} (dissoc-auto-attrs (attrs g :n1))))
    (is (= {:a 52} (dissoc-auto-attrs (attrs g :n2))))

    (is (not (has-edge? g [:n1 :in] [:n2 :out])))
    (add-edge [:n1 :in] [:n2 :out])
    (bind edgeid (find-edgeid g [:n1 :in] [:n2 :out]))
    (is (= ::pg/edge001 edgeid))
    (is (has-edge? g edgeid))
    (is (has-edge? g [:n1 :in] [:n2 :out]))

    (is (=sets #{::pg/edge001} (edges g)))

    (set-attr :n2 :a 12)
    (is (= 12 (attr g :n2 :a)))

    (set-attr [:n2 :out] [:n1 :in] :weight 1.0)
    (is (= 1.0 (attr g edgeid :weight)))
    (is (= 1.0 (attr g [:n1 :in] [:n2 :out] :weight)))
    (is {:weight 1.0} (dissoc-auto-attrs (attrs g edgeid)))
    (is {:weight 1.0} (dissoc-auto-attrs (attrs g [:n2 :out] [:n1 :in])))

    (set-attrs :n1 {:x 1, :y 2})
    (is (= {:x 1, :y 2} (dissoc-auto-attrs (attrs g :n1))))

    (set-attrs [:n2 :out] [:n1 :in] {:a 1, :b 2})
    (is (= {:a 1, :b 2} (dissoc-auto-attrs (attrs g edgeid))))))

(deftest test-neighbors
  (with-state [g (pgraph :n1 :n2 :n3)]
    (add-edge [:n1 :out] [:n2 :in])
    (add-edge [:n2 :out] [:n3 :in])
    (bind e1 (find-edgeid g [:n1 :out] [:n2 :in]))
    (bind e2 (find-edgeid g [:n2 :out] [:n3 :in]))
    (is (=sets [e1 e2] (edges g)))

    (is (has-edge? g e1))
    (is (not (has-edge? g :n1)))
    (is (not (has-edge? g :not-defined)))

    (is (=sets [e1] (incident-edges g :n1)))
    (is (=sets [e1 e2] (incident-edges g :n2)))

    (is (=sets [:out] (ports-of g :n1)))
    (is (=sets [:in :out] (ports-of g :n2)))

    (is (= #{[:n1 :out] [:n2 :in]} (incident-ports g e1)))
    (is (= #{[:n2 :out] [:n3 :in]} (incident-ports g e2)))

    (is (= :n2 (other-id g :n1 e1)))
    (is (= :n1 (other-id g :n2 e1)))
    (is (= :n3 (other-id g :n2 e2)))
    (is (= :n2 (other-id g :n3 e2)))

    (is (=sets [:n2] (neighbors-of g :n1)))
    (is (=sets [:n1 :n3] (neighbors-of g :n2)))))

(deftest test-edges-to-edges
  (with-state [g (pgraph :n1 :n2 :n3 :n4)]
    (setq e1 (add-edge-return-id [:n1 :out] [:n2 :in]))
    (setq e2 (add-edge-return-id [:n3 :out] [e1 :in]))
    (setq e3 (add-edge-return-id [:n4 :out] [e2 :in]))
    (setq e4 (add-edge-return-id [:n3 :out] [:n4 :in]))

    (is (= #{e1 e2 e3} (transitive-closure-of-edges-to-edges g :n1)))
    (is (= #{e1 e2 e3} (transitive-closure-of-edges-to-edges g :n2)))
    (is (= #{e2 e3 e4} (transitive-closure-of-edges-to-edges g :n3)))
    (is (= #{e3 e4}    (transitive-closure-of-edges-to-edges g :n4)))
    (is (= #{e1 e2 e3} (transitive-closure-of-edges-to-edges g e1)))
    (is (= #{e2 e3}    (transitive-closure-of-edges-to-edges g e2)))
    (is (= #{e3}       (transitive-closure-of-edges-to-edges g e3)))
    (is (= #{e4}       (transitive-closure-of-edges-to-edges g e4)))

    ;Removing the endpoint of an edge can cause a cascade of removals, if
    ;that edge was the endpoint of another edge.

    ;Removing nodes:
    -- (with-state [g g]
         (remove-node :n1)
         (is (=sets [:n2 :n3 :n4] (nodes g)))
         (is (=sets [e4] (edges g))))
    -- (with-state [g g]
         (remove-node :n2)
         (is (=sets [:n1 :n3 :n4] (nodes g)))
         (is (=sets [e4] (edges g))))
    -- (with-state [g g]
         (remove-node :n3)
         (is (=sets [:n1 :n2 :n4] (nodes g)))
         (is (=sets [e1] (edges g))))
    -- (with-state [g g]
         (remove-node :n4)
         (is (=sets [:n1 :n2 :n3] (nodes g)))
         (is (=sets [e1 e2] (edges g))))
    -- (with-state [g g]
         (remove-node :nonexistent)
         (is (=sets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=sets [e1 e2 e3 e4] (edges g))))

    ;Removing edges:
    -- (with-state [g g]
         (remove-edge e1)
         (is (=sets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=sets [e4] (edges g))))
    -- (with-state [g g]
         (remove-edge [:n1 :out] [:n2 :in])
         (is (=sets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=sets [e4] (edges g))))
    -- (with-state [g g]
         (remove-edge e2)
         (is (=sets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=sets [e1 e4] (edges g))))
    -- (with-state [g g]
         (remove-edge e3)
         (is (=sets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=sets [e1 e2 e4] (edges g))))
    -- (with-state [g g]
         (remove-edge e4)
         (is (=sets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=sets [e1 e2 e3] (edges g))))
    -- (with-state [g g]
         (remove-edge [:nonexistent1 :out] [:nonexistent1 :in])
         (is (=sets [e1 e2 e3 e4] (edges g))))))

(deftest test-niceties
  (with-state [g (pgraph)]
    (set-attr :n1 :a 1)  ;auto-create node
    (is (has-node? g :n1))
    (is (= 1 (attr g :n1 :a)))

    ;re-adding a node shouldn't affect its attrs
    (add-node :n1)
    (is (= 1 (attr g :n1 :a)))

    (set-attrs :n2 {:a 2})  ;auto-create :n2
    (is (has-node? g :n2))
    (is (= 2 (attr g :n2 :a)))

    (add-edge [:n2 :out] [:n3 :in])  ;auto-create :n3
    (is (has-node? g :n3))
    (is (has-edge? g [:n3 :in] [:n2 :out]))

    (set-attrs [:n4 :out] [:n5 :in] {:a 3})  ;auto-create :n4, :n5, edge
    (is (has-node? g :n4))
    (is (has-node? g :n5))
    (is (has-edge? g [:n4 :out] [:n5 :in]))
    (is (= 3 (attr g [:n4 :out] [:n5 :in] :a)))

    (set-attr [:n5 :out] [:n6 :in] :a 4)  ;auto-create :n6, edge
    (is (has-node? g :n6))
    (is (has-edge? g [:n5 :out] [:n6 :in]))
    (is (= 4 (attr g [:n5 :out] [:n6 :in] :a)))

    ;re-adding an edge shouldn't affect its attrs
    (add-edge [:n5 :out] [:n6 :in])
    (is (= 4 (attr g [:n5 :out] [:n6 :in] :a)))))

(deftest test-edn
  (with-state [g (pgraph :n1 :n2 :n3)]
    (add-edge [:n1 :out] [:n2 :in] {:a 3})
    (add-edge [:n2 :out] [:n3 :in])
    (set-attr :n1 :a 1)
    -- (dd (type g))
    -- (dd (pr-str g))
    ))
