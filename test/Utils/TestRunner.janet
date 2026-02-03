(var *passed* 0)
(var *failed* 0)
(var *suite-name* "Unknown Suite")

(defn start-suite [name]
  (set *suite-name* name)
  (set *passed* 0)
  (set *failed* 0)
  (print "Running suite: " name))

(defn assert [cond msg]
  (if cond
    (++ *passed*)
    (do
      (++ *failed*)
      (print "  FAIL: " msg)))
  cond)

(defn assert-error [f msg]
  (var threw false)
  (try
    (f)
    ([err] (set threw true)))
  (if threw
    (++ *passed*)
    (do
      (++ *failed*)
      (print "  FAIL: " msg " (Expected error, but none thrown)")))
  threw)

(defn end-suite []
  (let [total (+ *passed* *failed*)]
    (print (string/format "  %d passed, %d failed" *passed* *failed*))
    (if (> *failed* 0)
      (do
        (print (string/format "test suite %s FAILED" *suite-name*))
        (os/exit 1))
      (print (string/format "test suite %s passed (%d tests)" *suite-name* total)))))
