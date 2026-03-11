#!/usr/bin/env janet

(import ./matches :as m)
(import ./coreTT :as tt)

(defn sig/empty [] @{})

(defn sig/add-data [sig name params sort ctors]
  (put sig name {:kind :data
                 :name name
                 :params (or params @[])
                 :sort sort
                 :ctors (or ctors @[])})
  sig)

(defn sig/add-func [sig name params result core-type]
  (put sig name {:kind :func
                 :name name
                 :params (or params @[])
                 :result result
                 :type core-type})
  sig)

(defn sig/entry [sig name]
  (or (get sig name)
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
  (reduce
    (fn [out entry]
      (if (= (entry :kind) :data)
        (reduce (fn [acc ctor] (put acc (ctor :name) true)) out (entry :ctors))
        out))
    @{}
    (values sig)))

(defn vars [delta]
  (map |($ :name) delta))

(defn app-spine [name args]
  (reduce (fn [acc arg] (tt/tm/app acc (tt/tm/var arg)))
          (tt/tm/var name)
          args))

(defn build-lambda [body delta]
  (reduce (fn [inner _]
            (tt/tm/lam (fn [_] inner)))
          body
          (reverse delta)))

(defn sig/exact-ref [sig name]
  (let [e (sig/entry sig name)]
    (when (not= (e :kind) :func)
      (errorf "sig/exact-ref: '%v' is not a function" name))
    (let [delta (e :params)
          vs (vars delta)
          spine (app-spine name vs)]
      (build-lambda spine delta))))

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
   :sig/entry sig/entry
   :sig/params sig/params
   :sig/type-of sig/type-of
   :sig/ctors sig/ctors
   :sig/ctor sig/ctor
   :sig/ctor-name-set sig/ctor-name-set
   :sig/exact-ref sig/exact-ref
   :sig/available-ctors sig/available-ctors
   :sig/process-decl sig/process-decl
   :sig/build sig/build
   :vars vars
   :app-spine app-spine
   :build-lambda build-lambda})
