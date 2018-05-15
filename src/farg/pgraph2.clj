(ns farg.pgraph2
  "Port graphs that allow edges to link to edges"
  (:refer-clojure :exclude [rand rand-int cond pprint])
  (:require [better-cond.core :refer [cond]]
            [clojure.core.strint :refer [<<]]
            [clojure.tools.trace :refer [deftrace] :as trace]
            [com.rpl.specter :as S]
            [farg.pmatch :refer [pmatch]]
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
(def impl-attrs #{::id ::elem-type ::incident-ports})

(defn no-such-elem [id]
  (throw (IllegalArgumentException.
    (<< "pgraph has no elem ~{id}."))))

(defn no-such-edge [& args]
  (let [args (clojure.string/join \space args)]
    (throw (IllegalArgumentException.
      (<< "pgraph has no edge ~{args}.")))))

(defn- incident-set [[id1 p1] [id2 p2]]
  #{[id1 p1] [id2 p2]})

(defn find-edgeid [g [id1 p1] [id2 p2]]
  (S/select-one (S/keypath :edges (incident-set [id1 p1] [id2 p2])) g))

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

(defn- parse-id
  "Parses common arguments. Referred-to id need not exist."
 ([g id]
  [g id])
 ([g [id1 p1] [id2 p2]]
  [g (find-edgeid g [id1 p1] [id2 p2])]))

(defn- parse-id+1
 ([g id arg]
  [g id arg])
 ([g [id1 p1] [id2 p2] arg]
  [g (find-edgeid g [id1 p1] [id2 p2]) arg]))

(defn- existing-id+1
 ([g id arg]
  (if (has-elem? g id)
    [g id arg]
    (no-such-elem id)))
 ([g [id1 p1] [id2 p2] arg]
  (if-let [edgeid (find-edgeid g [id1 p1] [id2 p2])]
    [g edgeid arg]
    (no-such-edge [id1 p1] [id2 p2]))))

(defn elems [g]
  (S/select [:elems S/MAP-KEYS] g))

(defn nodes [g]
  (S/select [:elems S/MAP-VALS
             (S/selected? [::elem-type (S/pred= ::node)]) ::id] g))

(defn edges [g]
  (S/select [:elems S/MAP-VALS
             (S/selected? [::elem-type (S/pred= ::edge)]) ::id] g))

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
 ([g a1 a2]
  (throw (IllegalArgumentException.
    "Only 3 arguments passed to make-edge. Did you forget the stem?")))
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

(defn attr
 ([g id k]
  (S/select-one [:elems id k] g))
 ([g [id1 p1] [id2 p2] k]
  (when-let [edgeid (find-edgeid g [id1 p1] [id2 p2])]
    (attr g edgeid k))))

(defn set-attr
 ([g id k v]
  (if (has-elem? g id)
    (S/setval [:elems id k] v g)
    (no-such-elem id)))
 ([g [id1 p1] [id2 p2] k v]
  (cond
    :let [edgeid (find-edgeid g [id1 p1] [id2 p2])]
    (some? edgeid)
      (S/setval [:elems edgeid k] v g)
    (no-such-edge [id1 p1] [id2 p2]))))

#_(defn has-attr?
 ([g id k]
  (S/selected-any? [:elems id (S/must k)] g))
 ([g [id1 p1] [id2 p2] k]
  (when-let [edgeid (find-edgeid g [id1 p1] [id2 p2])]
    (has-attr? g edgeid k))))

(defn has-attr? [& args]
  (let [[g id k] (apply parse-id+1 args)]
    (S/selected-any? [:elems id (S/must k)] g)))

;Can't do variadic args for node/edge here
(defn update-attr [g id k f & args]
  (if (has-elem? g id)
    (S/transform [:elems id k] #(apply f % args) g)
    (no-such-elem id)))

(defn rm-attr [& args]
  (let [[g id k] (apply parse-id+1 args)]
    (if (has-elem? g id)
      (S/setval [:elems id k] S/NONE g)
      g)))

(defn attrs [& args]
  (let [[g id] (apply parse-id args)]
    (S/select-one [:elems id] g)))

(defn set-attrs [& args]
  (let [[g id as] (apply existing-id+1 args)]
    (S/transform [:elems id]
      #(merge (select-keys % impl-attrs) as)
      g)))

(defn user-attrs [& args]
  (apply dissoc (apply attrs args) impl-attrs))

(defn pgraph [& nodeids]
  (with-state [g (->PGraph {} {::edge 0} {} {})]
    (doseq [nodeid nodeids]
      (add-node nodeid))))

;;; Ports and neighbors

(defn elem->incident-edges [g id]
  (->> (S/select [:ports id S/MAP-VALS] g)
       (apply concat)))

(def node->incident-edges elem->incident-edges)

;TODO UT
(defn edge->incident-edges
 ([g edgeid]
  (elem->incident-edges g edgeid))
 ([g [id1 p1] [id2 p2]]
  (elem->incident-edges g (find-edgeid g [id1 p1] [id2 p2]))))

(defn port->incident-edges [g [id port-label]]
  (->> (S/select [:ports id port-label] g)
       (apply concat)))

(defn elem->port-labels [g id]
  (S/select [:ports id S/MAP-KEYS] g))

(def node->port-labels elem->port-labels)

;TODO UT
(defn edge->port-labels
 ([g edgeid]
  (elem->port-labels g edgeid))
 ([g [id1 p1] [id2 p2]]
  (elem->port-labels g (find-edgeid g [id1 p1] [id2 p2]))))

(defn elem->ports [g id]
  (map (fn [port-label] [id port-label])
       (elem->port-labels g id)))

(def node->ports elem->ports)

;TODO UT
(defn edge->ports
 ([g edgeid]
  (elem->ports g edgeid))
 ([g [id1 p1] [id2 p2]]
  (elem->ports g (find-edgeid g [id1 p1] [id2 p2]))))

(defn edge->incident-ports
 ([g edgeid]
  (S/select-one [:elems edgeid ::incident-ports] g))
 ([g [id1 p1] [id2 p2]]
  (edge->incident-ports g (find-edgeid g [id1 p1] [id2 p2]))))

(defn other-id
 ([g id edgeid]
  (cond
    :let [iset (edge->incident-ports g edgeid)]
    (empty? iset)
      nil
    :let [[iset-id _] (first iset)]
    (not= id iset-id)
      iset-id
    :let [[iset-id _] (second iset)]
    iset-id))
 ([g id [id1 p1] [id2 p2]]
  (other-id g id (find-edgeid g [id1 p1] [id2 p2]))))

(defn neighbors-of
 ([g id]
  (->> (elem->incident-edges g id)
       (map #(other-id g id %))
       distinct))
 ([g [id1 p1] [id2 p2]]
  (neighbors-of g (find-edgeid g [id1 p1] [id2 p2]))))
