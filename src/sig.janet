#!/usr/bin/env janet

(import ./matches :as m)
(import ./coreTT :as tt)

(defn sig/empty [] @{})

(defn sig/add-data [sig name params sort ctors]
  (put sig
       name
       {:kind :data
        :name name
        :params (or params @[])
        :sort sort
        :ctors (or ctors @[])})
  sig)

(defn sig/add-func [sig name params result core-type]
  (put sig
       name
       {:kind :func
        :name name
        :params (or params @[])
        :result result
        :type core-type})
  sig)

(defn sig/lookup [sig name]
  (get sig name))

(defn sig/entry [sig name]
  (or (sig/lookup sig name)
      (errorf "sig/entry: unknown name '%v'" name)))

(defn sig/params [sig name]
  ((sig/entry sig name) :params))

(defn sig/type-of [sig name]
  (let [e (sig/entry sig name)]
    (match (e :kind)
      :func (e :type)
      :data (e :sort)
      _ (errorf "sig/type-of: unsupported entry kind for '%v'" name))))

(defn sig/ctors [sig data-name]
  (let [e (sig/entry sig data-name)]
    (when (not= (e :kind) :data)
      (errorf "sig/ctors: '%v' is not a data declaration" data-name))
    (e :ctors)))

(defn sig/ctor [sig data-name ctor-name]
  (or (find |(= ($ :name) ctor-name) (sig/ctors sig data-name))
      (errorf "sig/ctor: unknown constructor '%v' in '%v'" ctor-name data-name)))

(defn sig/ctor-name-set [sig]
  (let [out @{}]
    (each entry (values sig)
      (when (= (entry :kind) :data)
        (each ctor (entry :ctors)
          (put out (ctor :name) true))))
    out))

(defn sig/delta-ref [sig name]
  (let [e (sig/entry sig name)]
    (when (not= (e :kind) :func)
      (errorf "sig/delta-ref: '%v' is not a function" name))
    (let [delta (e :params)
          n (length delta)]
      (defn build [i mk-app]
        (if (= i n)
          (mk-app (tt/tm/var name))
          (tt/tm/lam
           (fn [x]
             (build (+ i 1)
                    (fn [head]
                      (mk-app (tt/tm/app head x))))))))
      (build 0 (fn [head] head)))))

(defn sig/available-ctors [sig data-name type-args]
  (let [ctors (sig/ctors sig data-name)
        ctor-names (sig/ctor-name-set sig)]
    (m/ctors/available type-args ctors ctor-names)))

(defn sig/process-decl [sig decl]
  (match decl
    [:core/data name params sort ctors]
    (sig/add-data sig name params sort ctors)

    [:core/func name params result core-type _clauses]
    (sig/add-func sig name params result core-type)

    _ sig))

(defn sig/build [decls]
  (reduce sig/process-decl (sig/empty) decls))

(def exports
  {:sig/empty sig/empty
   :sig/add-data sig/add-data
   :sig/add-func sig/add-func
   :sig/lookup sig/lookup
   :sig/entry sig/entry
   :sig/params sig/params
   :sig/type-of sig/type-of
   :sig/ctors sig/ctors
   :sig/ctor sig/ctor
   :sig/ctor-name-set sig/ctor-name-set
   :sig/delta-ref sig/delta-ref
   :sig/available-ctors sig/available-ctors
   :sig/process-decl sig/process-decl
   :sig/build sig/build})
