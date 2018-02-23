(ns farg.pgraph
  "Port graphs that allow edges to link to edges"
  (:refer-clojure :exclude [rand rand-int cond pprint])
  (:require [better-cond.core :refer [cond]]
            [clojure.core.reducers :as r]
            [clojure.tools.trace :refer [deftrace] :as trace]
            [com.rpl.specter :as S]
            [farg.util :as util :refer [dd dde]]))

(defrecord PGraph
  ;"A port graph where edges can link to edges. elems is a map of the form
  ;{id attrs}. Each node and edge has a unique id in this map.
  ;
  ;stems is a stem-map, as defined in farg.util, for creating new node and
  ;edge ids by appending a number or letterstring to a stem.
  ;
  ;edges is a map {incident-ports id} where incident-ports is a set of
  ;[id p], i.e. port identifiers.
  [elems stems edges])

(defn pgraph []
  (->PGraph {} {::edge 0} {}))

(defn add-node
 ([g id]
  (add-node g id {}))
 ([g id attrs]
  (assoc-in g [:elems id] (merge attrs {::elem-type ::node ::id id}))))

(defn has-node? [g id]
  (cond
    :let [m (get-in g [:elems id])]
    (nil? m) false
    (= ::node (get m ::elem-type))))

(defn attr [g id k]
  (get-in g [:elems id k]))

(defn attrs [g id]
  (get-in g [:elems id]))

(defn- incident-set [[id1 p1] [id2 p2]]
  #{[id1 p1] [id2 p2]})

(defn add-edge [g [id1 p1] [id2 p2]]
  (cond
    :let [[stems edgeid] (util/next-id (get g :stems) ::edge)
          iset (incident-set [id1 p1] [id2 p2])]
    (-> g
        (assoc :stems stems)
        (assoc-in [:elems edgeid] {::elem-type ::edge ::id edgeid
                                   ::incident-ports iset})
        (assoc-in [:edges iset] edgeid))))

(defn find-edgeid [g [id1 p1] [id2 p2]]
  (get-in g [:edges #{[id1 p1] [id2 p2]}]))

(defn has-edge?
 ([g id]
  (cond
    :let [attrs (get-in g [:elems id])]
    (nil? attrs) nil
    (= ::edge (::elem-type attrs))))
 ([g [id1 p1] [id2 p2]]
  (contains? (get g :edges) (incident-set [:n1 :in] [:n2 :out]))))
