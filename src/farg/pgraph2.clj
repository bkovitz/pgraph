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

(defn elems [g]
  (S/select [:elems S/MAP-KEYS] g))

(defn nodes [g]
  (S/select [:elems S/MAP-VALS
             (S/selected? [::elem-type (S/pred= ::node)]) ::id] g))

(defn edges [g]
  (S/select [:elems S/MAP-VALS
             (S/selected? [::elem-type (S/pred= ::edge)]) ::id] g))

;;; Macros

(defmacro defidfunc [fname [g id & args] & body]
  `(defn ~fname
    ([~g ~id ~@args]
     ~@body)
    ([~g port1# port2# ~@args]
     (~fname ~g (find-edgeid ~g port1# port2#) ~@args))))

(defmacro defidfunc-mustexist [fname [g id & args] & body]
  `(defn ~fname
    ([~g ~id ~@args]
     (if (has-elem? ~g ~id)
       ~@body
       (no-such-elem ~id)))
    ([~g port1# port2# ~@args]
     (if-let [~id (find-edgeid ~g port1# port2#)]
       ~@body
       (no-such-edge port1# port2#)))))

(defmacro def3idfuncs [elemfunc nodefunc edgefunc [g id & args] & body]
  `(do
     (defidfunc ~elemfunc [~g ~id ~@args] ~@body)
     (defn ~nodefunc [~g ~id ~@args]
       (assert (let [type# (elem->type ~g ~id)]
                 (or (nil? type#) (= ::node type#)))
               (str ~id " is not a node."))
       ~@body)
     (defidfunc ~edgefunc [~g ~id ~@args]
       (assert (let [type# (elem->type ~g ~id)]
                 (or (nil? type#) (= ::edge type#)))
               (str ~id " is not an edge."))
       ~@body)))

;;; Making nodes and edges

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

(defn pgraph [& nodeids]
  (with-state [g (->PGraph {} {::edge 0} {} {})]
    (doseq [nodeid nodeids]
      (add-node nodeid))))

;;; Attrs

(defidfunc attr [g id k]
  (S/select-one [:elems id k] g))

(defidfunc-mustexist set-attr [g id k v]
  (S/setval [:elems id k] v g))

(defidfunc has-attr? [g id k]
  (S/selected-any? [:elems id (S/must k)] g))

;Can't do variadic args for node/edge here
(defn update-attr [g id k f & args]
  (if (has-elem? g id)
    (S/transform [:elems id k] #(apply f % args) g)
    (no-such-elem id)))

(defidfunc rm-attr [g id k]
  (if (has-elem? g id)
    (S/setval [:elems id k] S/NONE g)
    g))

(defidfunc attrs [g id]
  (S/select-one [:elems id] g))

(defidfunc-mustexist set-attrs [g id as]
  (S/transform [:elems id]
    #(merge (select-keys % impl-attrs) as)
    g))

(defn user-attrs [& args]
  (apply dissoc (apply attrs args) impl-attrs))

(defn gattrs
  "Returns map of whole-graph attrs."
  [g]
  (apply dissoc g impl-keys))

;;; Ports and neighbors

(defn port->elem [[id port-label]]
  id)

(defidfunc edge->incident-ports [g edgeid]
  (S/select-one [:elems edgeid ::incident-ports] g))

;TODO UT
(defidfunc edge->incident-elems [g edgeid]
  (map port->elem (edge->incident-ports g edgeid)))

;TODO UT
(defidfunc edge-as-map [g edgeid]
  (merge (attrs g edgeid)
         (->> (edge->incident-ports g edgeid)
              (map reverse)  ; (port-label id)
              (map vec)      ; [port-label id]
              (into {}))))

(def3idfuncs elem->incident-edges node->incident-edges edge->incident-edges
  [g id]
  (->> (S/select [:ports (S/must id) S/MAP-VALS] g)
       (apply concat)))

(defn port->incident-edges [g [id port-label]]
  (->> (S/select [:ports id port-label] g)
       (apply concat)))

(def3idfuncs elem->port-labels node->port-labels edge->port-labels [g id]
  (S/select [:ports id S/MAP-KEYS] g))

(def3idfuncs elem->ports node->ports edge->ports [g id]
  (map (fn [port-label] [id port-label])
       (elem->port-labels g id)))

(defidfunc other-id [g id edgeid]
  (cond
    :let [iset (seq (edge->incident-ports g edgeid))]
    (empty? iset)
      nil
    :let [[iset-id _] (first iset)]
    (not= id iset-id)
      iset-id
    :let [[iset-id _] (second iset)]
    iset-id))

;TODO UT
(defn other-port [g [id port-label :as port] edgeid]
  (cond
    :let [ports (seq (edge->incident-ports g edgeid))]
    (empty? ports)
      nil
    :let [that-port (first ports)]
    (not= port that-port)
      that-port
    (second ports)))

(defidfunc elem->neighbors
  ;"Returns lazy seq of all elems connected by an edge to any port of id."
  [g id]
  (->> (elem->incident-edges g id)
       (map #(other-id g id %))
       distinct))

(defidfunc elem->neighbor?
  ;"Returns logical true iff thatid is connected by an edge to any port of id."
  [g id thatid]
  (some #{thatid} (elem->neighbors g id)))

;TODO UT
(defn port->neighbors
  "Returns lazy seq of all elems connected by an edge to [id port-label]."
  [g [id port-label :as port]]
  (->> (port->incident-edges g port)
       (map #(other-id g id %))
       distinct))

;TODO UT
(defn port->neighboring-ports
  "Returns lazy seq of all ports connected by an edge to [id port-label]."
  [g [id port-label :as port]]
  (->> (port->incident-edges g port)
       (map #(other-port g port %))
       distinct))

;;; Removing elements

(defidfunc transitive-closure-of-edges-to-edges [g id]
  (loop [so-far (if (has-edge? g id) #{id} #{})
         to-do (into #{} (elem->incident-edges g id))]
    (cond
      (empty? to-do)
        so-far
      :let [edgeid (first to-do)]
      (recur (conj so-far edgeid)
             (clojure.set/difference
               (clojure.set/union (disj to-do edgeid)
                                  (set (elem->incident-edges g edgeid)))
               so-far)))))

(defn- rm-edge-from-port [g [id port-label] edgeid]
  (cond
    :let [g (S/setval [:ports id port-label (S/set-elem edgeid)] S/NONE g)
          new-set (S/select-one [:ports id port-label] g)]
    (not (empty? new-set))
      g
    :let [g (S/setval [:ports id port-label] S/NONE g)
          new-map (S/select-one [:ports id] g)]
    (not (empty? new-map))
      g
    (S/setval [:ports id] S/NONE g)))

(defn- remove-edge* [g edgeid]
  (cond
    :let [iset (edge->incident-ports g edgeid)]
    (empty? iset)
      g
    :let [g (reduce (fn [g port] (rm-edge-from-port g port edgeid))
                    g
                    (seq iset))]
    (->> g
         (S/setval (S/keypath :edges iset) S/NONE)
         (S/setval [:elems edgeid] S/NONE))))

(def3idfuncs remove-elem remove-node remove-edge [g id]
  ;TODO Post Specter issue: (S/setval [:elems nil] S/NONE) rms :elems
  (if (some? id)
    (->> (reduce remove-edge* g (transitive-closure-of-edges-to-edges g id))
         (S/setval [:elems id] S/NONE))
    g))

;;; Printing

;TODO UT
(defn attrstr [g id]
  (let [as (user-attrs g id)]
    (if (empty? as) "" (str \space (map-str as)))))

;TODO UT
(defn edgestr [g edgeid]
  (with-out-str
    (print (str edgeid \space))
    (cond
      :let [ports (edge->incident-ports g edgeid)]
      (= 1 (count ports))
        (pr (first ports) (first ports))
      :do (print (->> ports (map pr-str) sort (clojure.string/join \space)))
      :do (print (attrstr g edgeid)))))

;TODO UT
(defn pprint-nodes [g]
  (cond
    :let [ns (sort-by str (nodes g))]
    (empty? ns)
      (println "Nodes: None")
    (do
      (println "Nodes:")
      (doseq [node ns]
        (println (str "  " node (attrstr g node)))))))

;TODO UT
(defn pprint-edges [g]
  (cond
    :let [es (sort-by str (edges g))]
    (empty? es)
      (println "Edges: None")
    (do
      (println "Edges:")
      (doseq [s (->> es (map #(edgestr g %)))]
        (println \space s)))))

;TODO UT
(defn pprint [g]
  (println "Gattrs:" (gattrs g))
  (pprint-nodes g)
  (pprint-edges g))
