(ns farg.pgraph
  "Port graphs that allow edges to link to edges"
  (:refer-clojure :exclude [rand rand-int cond pprint])
  (:require [better-cond.core :refer [cond]]
            [clojure.core.reducers :as r]
            [clojure.core.strint :refer [<<]]
            [clojure.tools.trace :refer [deftrace] :as trace]
            [com.rpl.specter :as S]
            [farg.util :as util :refer [dd dde map-str]]
            [farg.with-state :refer [with-state]]
            [potemkin :refer [def-map-type]]))

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

(defn- incident-set [[id1 p1] [id2 p2]]
  #{[id1 p1] [id2 p2]})

;TODO UT
(defn port->node
  "Returns the node that owns a port."
  [[node _ :as port]]
  node)

(defn next-id
  "Returns [g id] where id is a new, unique id starting with stem."
  [g stem]
  (let [elems (get g :elems)
        [stems id] (loop [stems (get g :stems)]
                     (let [[stems id] (util/next-id stems stem)]
                       (if (contains? elems id)
                         (recur stems)
                         [stems id])))]
    [(assoc g :stems stems) id]))

(declare add-nodes)

(defn pgraph [& nodes]
  (apply add-nodes (->PGraph {} {::edge 0} {} {}) nodes))

(def auto-attrs #{::elem-type ::id ::incident-ports})

(defn dissoc-auto-attrs [m]
  (apply dissoc m auto-attrs))

(defn select-auto-attrs [m]
  (select-keys m auto-attrs))

(defn has-elem? [g id]
  (contains? (get g :elems) id))

(defn elem-type [g id]
  (S/select-one [:elems id ::elem-type] g))

(defn find-edgeid [g [id1 p1] [id2 p2]]
  (get-in g [:edges #{[id1 p1] [id2 p2]}]))

(defn- find-attrs
 ([g id]
  (get-in g [:elems id]))
 ([g [id1 p1] [id2 p2]]
  (find-attrs g (find-edgeid g [id1 p1] [id2 p2]))))

(defn- add-node* [g id attrs]
  (assoc-in g [:elems id] (merge attrs {::elem-type ::node ::id id})))

(defn- add-edge*
  "Returns [g new-edgeid]."
 ([g [id1 p1] [id2 p2]]
  (add-edge* g [id1 p1] [id2 p2] ::edge))
 ([g [id1 p1] [id2 p2] stem]
  (let [[g edgeid] (next-id g stem)
        iset (incident-set [id1 p1] [id2 p2])
        g (-> g
          (assoc-in [:elems edgeid] {::elem-type ::edge, ::id edgeid,
                                     ::incident-ports iset})
          (assoc-in [:edges iset] edgeid)
          (update-in [:ports id1 p1] (fnil conj #{}) edgeid)
          (update-in [:ports id2 p2] (fnil conj #{}) edgeid))]
    [g edgeid])))

(defn add-node
 ([g id]
  (add-node g id {}))
 ([g id attrs]
  (let [old-attrs (find-attrs g id)]
    (case (get old-attrs ::elem-type)
      nil
        (assoc-in g [:elems id] (merge attrs {::elem-type ::node ::id id}))
      ::node
        (assoc-in g [:elems id] (merge old-attrs attrs))
        ))))

(defn add-nodes [g & ids]
  (reduce add-node g ids))

(defn- force-id
  "Returns g, adding a node without attrs for id if necessary."
  [g id]
  (if (nil? (elem-type g id))
    (add-node g id)
    g))

(defn- force-elem
  "Returns [g attrs], creating an element if necessary."
 ([g id]
  (cond
    :let [attrs (find-attrs g id)]
    (nil? attrs)
      (let [g (add-node* g id {})]
        [g (find-attrs g id)])
    [g attrs]))
 ([g [id1 p1] [id2 p2]]
  (cond
    :let [old-attrs (find-attrs g [id1 p1] [id2 p2])]
    (nil? old-attrs)
      (let [[g edgeid] (-> g
                           (force-id id1)
                           (force-id id2)
                           (add-edge* [id1 p1] [id2 p2]))]
        [g (find-attrs g edgeid)])
    [g old-attrs])))

(defn nodes
  "Returns lazy seq of node ids."
  [g]
  (->> (get g :elems)
       (filter (fn [[id attrs]] (= ::node (get attrs ::elem-type))))
       (map first)))

(defn edges
  "Returns seq of edge ids."
  [g]
  (-> g :edges vals))

;TODO UT
(defn elems
  "Returns all elements of graph g: just their ids, not their attrs."
  [g]
  (-> g :elems keys))

(defn has-node? [g id]
  (cond
    :let [attrs (get-in g [:elems id])]
    (nil? attrs) false
    (= ::node (get attrs ::elem-type))))

(defn attr
 ([g id k]
  (get-in g [:elems id k]))
 ([g [id1 p1] [id2 p2] k]
  (attr g (find-edgeid g [id1 p1] [id2 p2]) k)))

(defn attrs
 ([g id]
  (get-in g [:elems id]))
 ([g [id1 p1] [id2 p2]]
  (attrs g (find-edgeid g [id1 p1] [id2 p2]))))

;TODO UT
(defn user-attrs
  [& args]
  (-> (apply attrs args)
      dissoc-auto-attrs))

(defn set-attr
 ([g id k v]
  (let [[g attrs] (force-elem g id)]
    (assoc-in g [:elems id] (assoc attrs k v))))
 ([g [id1 p1] [id2 p2] k v]
  (let [[g attrs] (force-elem g [id1 p1] [id2 p2])]
    (set-attr g (find-edgeid g [id1 p1] [id2 p2]) k v))))

;TODO UT
(defn update-attr
  [g id k f & args]
  (let [[g attrs] (force-elem g id)]
    (assoc-in g [:elems id] (apply update attrs k f args))))

;TODO UT
(defn update-edge-attr
  [g [id1 p1] [id2 p2] k f & args]
  (let [[g attrs] (force-elem g [id1 p1] [id2 p2])
        edgeid (find-edgeid g [id1 p1] [id2 p2])]
    (assoc-in g [:elems edgeid] (apply update attrs k f args))))

(defn weight [g id]
  (cond
    :let [w (attr g id :weight)]
    (nil? w)
      0.0
    w))

(defn add-weight [g id delta]
  (set-attr g id :weight (+ delta (weight g id))))

(defn set-attrs
 ([g id new-attrs]
  (let [[g old-attrs] (force-elem g id)]
    (assoc-in g [:elems id] (merge (select-auto-attrs old-attrs) new-attrs))))
 ([g [id1 p1] [id2 p2] new-attrs]
  (let [[g old-attrs] (force-elem g [id1 p1] [id2 p2])
        id (find-edgeid g [id1 p1] [id2 p2])]
    (assoc-in g [:elems id] (merge (select-auto-attrs old-attrs) new-attrs)))))

(defn merge-default-attrs
 ([g id default-attrs]
  (set-attrs g id (merge default-attrs (attrs g id))))
 ([g id default-attrs1 default-attrs2 & more]
  (merge-default-attrs g id (apply merge default-attrs1 default-attrs2 more))))

(defn has-edge?
 ([g id]
  (= ::edge (attr g id ::elem-type)))
 ([g [id1 p1] [id2 p2]]
  (contains? (get g :edges) (incident-set [id1 p1] [id2 p2]))))

(defn add-edge-return-id [g [id1 p1] [id2 p2]]
  (with-state [g g]
    (when (nil? (elem-type g id1))
      (add-node id1))
    (when (nil? (elem-type g id2))
      (add-node id2))
    (bind edgeid (find-edgeid g [id1 p1] [id2 p2]))
    (if (nil? edgeid)
      (add-edge* [id1 p1] [id2 p2])
      (return [g edgeid]))))

(defn add-edge
 ([g [id1 p1] [id2 p2]]
  (let [[g _] (add-edge-return-id g [id1 p1] [id2 p2])]
    g))
 ([g [id1 p1] [id2 p2] attrs] ;TODO UT this arity
  (cond
    :let [existing-edgeid (find-edgeid g [id1 p1] [id2 p2])]
    (some? existing-edgeid)
      (set-attrs g [id1 p1] [id2 p2] attrs)
    :let [stem (get attrs :class)] ;HACK pgraph shouldn't know :class
    (nil? stem)
      (set-attrs g [id1 p1] [id2 p2] attrs)
    (with-state [g g]
      (setq edgeid (add-edge* [id1 p1] [id2 p2] stem))
      (set-attrs edgeid attrs)))))

(defn port-labels-of
 ([g id]
  (S/select [:ports id S/MAP-KEYS] g)))

(defn elem->incident-edges
 ([g id]
  (->> (S/select [:ports id S/MAP-VALS] g)
       (apply concat))))

;TODO UT
(defn port->incident-edges
  [g [id port-label]]
  (->> (S/select [:ports id port-label] g)
       (apply concat)))

(defn incident-ports
  "Set of [id port-label]'s incident to given edge."
 ([g edgeid]
  (S/select-one [:elems edgeid ::incident-ports] g)))

(def edge->incident-ports incident-ports)

;TODO UT
(defn incident-elems
  "Seq of elems (nodes and/or edges) incident to a given edge."
 ([g edgeid]
  (map port->node (incident-ports g edgeid))))

;TODO UT
(defn edge-as-map
  "Returns map {mate1's-port-label mate1-id, mate2's-port-label mate2-id} plus
  all of the edge's attrs."
  [fm edgeid]
  (merge (attrs fm edgeid)
         (->> (incident-ports fm edgeid)
              (map reverse)
              (map vec)
              (into {}))))

(defn other-id
  "The id at an endpoint of the edge named by edgeid, other than 'id'."
  [g id edgeid]
  (loop [iset (incident-ports g edgeid)]
    (cond
      (empty? iset) nil
      :let [[iset-id _] (first iset)]
      (not= id iset-id) iset-id
      (recur (rest iset)))))

;TODO UT
(defn other-port
  "The port at an endpoint of the edge named by edgeid, other than 'port'."
  [g [id port-label :as port] edgeid]
  (loop [ports (seq (incident-ports g edgeid))]
    (cond
      (empty? ports) nil
      :let [that-port (first ports)]
      (not= port that-port) that-port
      (recur (rest ports)))))

(defn neighbors-of [g id]
  (->> (elem->incident-edges g id)
       (map #(other-id g id %))
       distinct))

;TODO UT
(defn neighbor-of? [g thisid thatid]
  (some #{thatid} (neighbors-of g thisid)))

(defn neighboring-edges-of
  "Neighbors that are edges."
  [g id]
  (->> (neighbors-of g id)
       (filter #(has-edge? g %))
       set))

;TODO UT
(defn neighbor-via
  "Returns the id of the elem connected by an edge to [id port-label], or
  nil if none. If more than one edge is incident to [id port-label],
  arbitrarily chooses the \"first\"."
  [g [id port-label :as port]]
  (cond
    :let [edgeid (first (port->incident-edges g port))]
    (nil? edgeid)
      nil
    (other-id g id edgeid)))

;TODO UT
(defn neighbors-via
  "Returns lazy seq of all elems connected by an edge to [id port-label]."
  [g [id port-label :as port]]
  (->> (port->incident-edges g port)
       (map #(other-id g id %))
       distinct))

(def port->neighbor neighbor-via)
(def port->neighbors neighbors-via)

;TODO UT
(defn port->neighboring-ports
  "Returns lazy seq of all ports connected by an edge to [id port-label]."
  [g [id port-label :as port]]
  (->> (port->incident-edges g port)
       (map #(other-port g port %))
       distinct))

;;; gattrs: An attribute map that applies to the pgraph as a whole.

(defn gattrs [g]
  (apply dissoc g impl-keys)
  #_(get g :gattrs))

;TODO rm
(defn set-gattr [g k v]
  (assoc-in g [:gattrs k] v))

;TODO rm
(defn gattr [g k]
  (get-in g [:gattrs k]))

;TODO rm
(defn set-gattrs [g m]
  (assoc g :gattrs m))

;;; printing

(defn attrstr [g id]
  (let [as (dissoc-auto-attrs (attrs g id))]
    (if (empty? as) "" (str \space (map-str as)))))

(defn edgestr [g edgeid]
  (with-out-str
    (print (str edgeid \space))
    (cond
      :let [ports (incident-ports g edgeid)]
      (= 1 (count ports))
        (pr (first ports) (first ports))
      :do (print (->> ports (map pr-str) sort (clojure.string/join \space)))
      :do (print (attrstr g edgeid)))))

(defn pprint-nodes [g]
  (cond
    :let [ns (sort-by str (nodes g))]
    (empty? ns)
      (println "Nodes: None")
    (do
      (println "Nodes:")
      (doseq [node ns]
        (println (str "  " node (attrstr g node)))))))

(defn pprint [g]
  (println "Gattrs:" (gattrs g))
  (cond
    :let [ns (sort-by str (nodes g))]
    (empty? ns)
      (println "Nodes: None\nEdges: None")
    :do (do
          (println "Nodes:")
          (doseq [node ns]
            (println (str "  " node (attrstr g node)))))
    :let [es (sort-by str (edges g))]
    (empty? es)
      (println "Edges: None")
    :do (do
          (println "Edges:")
          (doseq [s (->> es (map #(edgestr g %)) sort)]
            (println \space s)))))

(defn transitive-closure-of-edges-to-edges
 ([g id]
  (loop [so-far (if (has-edge? g id) #{id} #{})
         to-do (into #{} (elem->incident-edges g id))]
    (cond
      (empty? to-do) so-far
      :let [edgeid (first to-do)]
      (recur (conj so-far edgeid)
             (clojure.set/difference
               (clojure.set/union (disj to-do edgeid)
                                  (set (elem->incident-edges g edgeid)))
               so-far))))))

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

(defn remove-edge* [g edgeid]
  (cond
    :let [iset (S/select-one [:elems edgeid ::incident-ports] g)]
    (nil? iset)
      g
    :let [g (reduce (fn [g port] (rm-edge-from-port g port edgeid))
                    g
                    (seq iset))]
    (->> g
      (S/setval [:edges (S/keypath iset)] S/NONE)
      (S/setval [:elems edgeid] S/NONE))))

(defn remove-edge
 ([g edgeid]
  (reduce remove-edge* g (transitive-closure-of-edges-to-edges g edgeid)))
 ([g port1 port2]
  (remove-edge g (find-edgeid g port1 port2))))

(defn remove-node
  [g id]
  (->> (reduce remove-edge* g (transitive-closure-of-edges-to-edges g id))
    (S/setval [:elems id] S/NONE)))

;TODO UT
(defn remove-elem
  [g id]
  (case (elem-type g id)
    ::node
      (remove-node g id)
    ::edge
      (remove-edge g id)
    nil
      g))

;TODO Include the gattrs.
(defn as-seq [g]
  (for [m (->> g (S/select [:elems S/MAP-VALS]) (sort-by #(-> % ::id str)))]
    (let [id (::id m), as (dissoc-auto-attrs m)]
      (case (::elem-type m)
        ::node
          (if (empty? as) (list 'node id) (list 'node id as))
        ::edge
          (let [iset (sort-by str (::incident-ports m))]
            (if (empty? as) `(~'edge ~id ~@iset) `(~'edge ~id ~@iset ~as)))))))

;;; edn

(defn pgraph->edn [g]
  (str "#farg.pgraph/pgraph["
       (clojure.string/join \space (as-seq g))
       "]"))

(defmethod print-method PGraph [g ^java.io.Writer w]
  (.write w (<< "#PGraph[nodes ~(count (nodes g)), edges ~(count (edges g))]")))

(defmethod print-dup PGraph [v ^java.io.Writer w]
  (.write w (pgraph->edn v)))

(defn vec->pgraph [v]
  (dd v)
  v)

(def edn-readers {'farg.pgraph/pgraph vec->pgraph})
