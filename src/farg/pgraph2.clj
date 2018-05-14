(ns farg.pgraph2
  "Port graphs that allow edges to link to edges"
  (:refer-clojure :exclude [rand rand-int cond pprint])
  (:require [better-cond.core :refer [cond]]
            [clojure.core.strint :refer [<<]]
            [clojure.tools.trace :refer [deftrace] :as trace]
            [com.rpl.specter :as S]
            [farg.util :as util :refer [dd dde map-str]]
            [farg.with-state :refer [with-state]]))

(defrecord PGraph
  ;"A port graph where edges can link to edges.
  ;
  ;elems is a map of the form {id attrs}. Each node and edge has a unique id
  ;in this map.
  ;
  ;For each elem, attrs gets automatic keys ::elem-type (value: either
  ;::edge or ::node) and ::id (value: the elem's key in the elems map).
  ;
  ;stems is a stem-map, as defined in farg.util, for creating new node and
  ;edge ids by appending a number or letterstring to a stem.
  ;
  ;edges is a map {incident-ports id} where incident-ports is a set of
  ;[id p], i.e. port identifiers.
  ;
  ;ports is a map {id {port-label #{edge-ids...}}}.
  [elems stems edges ports])

(def impl-keys #{:elems :stems :edges :ports})
(def impl-attrs #{::id ::elem-type})

(defn no-such-elem [id]
  (throw (IllegalArgumentException.
    (<< "pgraph has no elem ~{id}."))))

(defn- incident-set [[id1 p1] [id2 p2]]
  #{[id1 p1] [id2 p2]})

(defn find-edgeid [g [id1 p1] [id2 p2]]
  (S/select-one (S/keypath :edges (incident-set [id1 p1] [id2 p2])) g))

(defn elems [g]
  (S/select [:elems S/MAP-KEYS] g))

(defn nodes [g]
  (S/select [:elems S/MAP-VALS
             (S/selected? [::elem-type (S/pred= ::node)]) ::id] g))

(defn edges [g]
  (->> (get g :elems)
       (filter #(= (::elem-type %) ::edge))
       (map first)))

(defn has-elem? [g id]
  (S/selected-any? [:elems (S/must id)] g))

(defn has-node? [g id]
  (S/selected-any? [:elems (S/must id) ::elem-type (S/pred= ::node)] g))

(defn has-edge?
 ([g id]
  (S/selected-any? [:elems (S/must id) ::elem-type (S/pred= ::edge)] g))
 ([g [id1 p1] [id2 p2]]
  (find-edgeid g [id1 p1] [id2 p2])))

(defn elem->type [g id]
  (S/select-one [:elems id ::elem-type] g))

(defn- next-id
  "Returns [g id] where id is a new, unique id starting with stem."
  [g stem]
  (let [elems (get g :elems)
        [stems id] (loop [stems (get g :stems)]
                     (let [[stems id] (util/next-id stems stem)]
                       (if (contains? elems id)
                         (recur stems)
                         [stems id])))]
    [(assoc g :stems stems) id]))

(defn make-node
 ([g stem]
  (make-node g stem {}))
 ([g stem attrs]
  (let [[g id] (next-id g stem)
        g (S/setval [:elems id] (merge {::id id, ::elem-type ::node} attrs) g)]
    [g id])))

(defn add-node [& args]
  (first (apply make-node args)))

(defn make-edge
 ([g stem [id1 p1] [id2 p2]]
  (make-edge g stem [id1 p1] [id2 p2] {}))
 ([g stem [id1 p1] [id2 p2] attrs]
  (cond
    :let [edgeid (find-edgeid g [id1 p1] [id2 p2])]
    (some? edgeid)
      [g edgeid]
    (not (has-elem? g id1))
      (no-such-elem id1)
    (not (has-elem? g id2))
      (no-such-elem id2)
    :let [[g edgeid] (next-id g (or stem ::edge))
          iset (incident-set [id1 p1] [id2 p2])
          g (->> g
                 (S/setval [:elems edgeid] 
                           (merge {::elem-type ::edge, ::id edgeid,
                                   ::incident-ports iset} attrs))
                 (S/setval (S/keypath :edges iset) edgeid)
                 (S/transform [:ports id1 p1] #(conj (or % #{}) edgeid))
                 (S/transform [:ports id2 p2] #(conj (or % #{}) edgeid)))]
    [g edgeid])))

(defn add-edge [& args]
  (first (apply make-edge args)))

(defn attr [g id k]
  (S/select-one [:elems id k] g))

(defn set-attr [g id k v]
  (S/setval [:elems id k] v g))

(defn has-attr? [g id k]
  (S/selected-any? [:elems id (S/must k)] g))

(defn update-attr [g id k f & args]
  (if (has-elem? g id)
    (S/transform [:elems id k] #(apply f % args) g)
    (no-such-elem id)))

(defn rm-attr [g id k]
  (S/setval [:elems id k] S/NONE g))

(defn attrs [g id]
  (S/select-one [:elems id] g))

(defn user-attrs [g id]
  (apply dissoc (attrs g id) impl-attrs))

(defn pgraph [& nodeids]
  (with-state [g (->PGraph {} {::edge 0} {} {})]
    (doseq [nodeid nodeids]
      (add-node nodeid))))
