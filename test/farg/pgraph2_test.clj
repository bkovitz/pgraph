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
    (is (not (has-attr? g [:n1 :in] [:n2 :out] :x)))
    
    ;It's not an error to remove an attr from a nonexistent id
    (rm-attr :non-existent :a)
    (rm-attr [:no :port] [:nothing :port] :a)
    ))

(deftest test-neighbors
  (with-state [g (pgraph :n1 :n2 :n3)]
    (add-edge nil [:n1 :out] [:n2 :in])
    (add-edge nil [:n2 :out] [:n3 :in])
    (bind e1 (find-edgeid g [:n1 :out] [:n2 :in]))
    (bind e2 (find-edgeid g [:n2 :out] [:n3 :in]))
    (is (=msets [e1 e2] (edges g)))

    (is (has-edge? g e1))
    (is (not (has-edge? g :n1)))
    (is (not (has-edge? g :not-defined)))

    (is (=msets [e1] (elem->incident-edges g :n1)))
    (is (=msets [e1 e2] (elem->incident-edges g :n2)))
    (is (empty? (elem->incident-edges g :non-existent)))
    (is (empty? (elem->incident-edges g nil)))

    (is (= [e1] (port->incident-edges g [:n1 :out])))
    (is (= [e1] (port->incident-edges g [:n2 :in])))
    (is (= [e2] (port->incident-edges g [:n2 :out])))
    (is (= [e2] (port->incident-edges g [:n3 :in])))

    (is (=msets [:out] (elem->port-labels g :n1)))
    (is (=msets [:in :out] (elem->port-labels g :n2)))

    (is (=msets [[:n1 :out]] (elem->ports g :n1)))

    (is (= #{[:n1 :out] [:n2 :in]} (edge->incident-ports g e1)))
    (is (= #{[:n2 :out] [:n3 :in]} (edge->incident-ports g e2)))
    (is (empty? (edge->incident-ports g nil)))

    (is (= :n2 (other-id g :n1 e1)))
    (is (= :n1 (other-id g :n2 e1)))
    (is (= :n3 (other-id g :n2 e2)))
    (is (= :n2 (other-id g :n3 e2)))

    (is (=msets [:n2] (neighbors-of g :n1)))
    (is (=msets [:n1 :n3] (neighbors-of g :n2)))))

(deftest test-edges-to-edges
  (with-state [g (pgraph :n1 :n2 :n3 :n4)]
    (setq e1 (make-edge nil [:n1 :out] [:n2 :in]))
    (setq e2 (make-edge nil [:n3 :out] [e1 :in]))
    (setq e3 (make-edge nil [:n4 :out] [e2 :in]))
    (setq e4 (make-edge nil [:n3 :out] [:n4 :in]))

    (is (= #{e1 e2 e3} (transitive-closure-of-edges-to-edges g :n1)))
    (is (= #{e1 e2 e3} (transitive-closure-of-edges-to-edges g :n2)))
    (is (= #{e2 e3 e4} (transitive-closure-of-edges-to-edges g :n3)))
    (is (= #{e3 e4}    (transitive-closure-of-edges-to-edges g :n4)))
    (is (= #{e1 e2 e3} (transitive-closure-of-edges-to-edges g e1)))
    (is (= #{e2 e3}    (transitive-closure-of-edges-to-edges g e2)))
    (is (= #{e3}       (transitive-closure-of-edges-to-edges g e3)))
    (is (= #{e4}       (transitive-closure-of-edges-to-edges g e4)))
    (is (= #{}         (transitive-closure-of-edges-to-edges g :nonexistent)))
    (is (= #{}         (transitive-closure-of-edges-to-edges g nil)))

    ;Removing the endpoint of an edge can cause a cascade of removals, if
    ;that edge was the endpoint of another edge.

    ;Removing nodes:
    -- (with-state [g g]
         (remove-node :n1)
         (is (=msets [:n2 :n3 :n4] (nodes g)))
         (is (=msets [e4] (edges g))))
    -- (with-state [g g]
         (remove-node :n2)
         (is (=msets [:n1 :n3 :n4] (nodes g)))
         (is (=msets [e4] (edges g))))
    -- (with-state [g g]
         (remove-node :n3)
         (is (=msets [:n1 :n2 :n4] (nodes g)))
         (is (=msets [e1] (edges g))))
    -- (with-state [g g]
         (remove-node :n4)
         (is (=msets [:n1 :n2 :n3] (nodes g)))
         (is (=msets [e1 e2] (edges g))))
    -- (with-state [g g]
         (remove-node :nonexistent)
         (is (=msets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=msets [e1 e2 e3 e4] (edges g))))

    ;Removing edges:
    -- (with-state [g g]
         (remove-edge e1)
         (is (=msets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=msets [e4] (edges g))))
    -- (with-state [g g]
         (remove-edge [:n1 :out] [:n2 :in])
         (is (=msets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=msets [e4] (edges g))))
    -- (with-state [g g]
         (remove-edge e2)
         (is (=msets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=msets [e1 e4] (edges g))))
    -- (with-state [g g]
         (remove-edge e3)
         (is (=msets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=msets [e1 e2 e4] (edges g))))
    -- (with-state [g g]
         (remove-edge e4)
         (is (=msets [:n1 :n2 :n3 :n4] (nodes g)))
         (is (=msets [e1 e2 e3] (edges g))))
    -- (with-state [g g]
         (remove-edge [:nonexistent1 :out] [:nonexistent1 :in])
         (is (=msets [e1 e2 e3 e4] (edges g))))))

(deftest test-gattrs
  (with-state [g (pgraph :ignored1 :ignored2)]
    (is (= {} (pg/gattrs g)))
    ;(pg/set-gattr :most-recent-x 22)
    (assoc :most-recent-x 22)
    ;(is (= 22 (pg/gattr g :most-recent-x)))
    (is (= 22 (get g :most-recent-x)))
    ;(pg/set-gattrs {:a 1})
    #_(is (= {:a 1} (pg/gattrs g)))))
