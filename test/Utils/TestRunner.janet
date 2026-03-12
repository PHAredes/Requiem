(var current-suite nil)

(defn env/int [name fallback]
  (let [raw (os/getenv name)]
    (if raw (scan-number raw) fallback)))

(defn start-suite [name]
  (printf "Running suite: %s" name)
  (let [seed (os/getenv "TEST_SEED")
        trials (os/getenv "TEST_TRIALS")]
    (when seed
      (print "  seed:" seed))
    (when trials
      (print "  trials override:" trials)))
  (set current-suite @{:name name :passed 0 :failed 0})
  current-suite)

(defn- resolve-suite-args [args]
  (case (length args)
    2 [current-suite (args 0) (args 1)]
    3 [(args 0) (args 1) (args 2)]
    (errorf "invalid assert invocation: %v" args)))

(defn assert [& args]
  (let [[suite cond msg] (resolve-suite-args args)]
    (if cond
      (update suite :passed inc)
      (do
        (update suite :failed inc)
        (print "  FAIL: " msg)))
    cond))

(defn assertf [suite cond msg details]
  (if cond
    (update suite :passed inc)
    (do
      (update suite :failed inc)
      (print "  FAIL: " msg)
      (when details
        (print "    " details))))
  cond)

(defn property-count [fallback]
  (env/int "TEST_TRIALS" fallback))

(defn assert-error [& args]
  (let [[suite f msg expected-msg]
        (case (length args)
          2 [current-suite (args 0) (args 1) nil]
          3 [(args 0) (args 1) (args 2) nil]
          4 [(args 0) (args 1) (args 2) (args 3)]
          (errorf "invalid assert-error invocation: %v" args))]
    (var threw false)
    (var actual-msg nil)
    (try
      (f)
      ([err]
        (set threw true)
        (set actual-msg (string err))))
    (if threw
      (if (or (nil? expected-msg)
              (not (nil? (string/find expected-msg actual-msg))))
        (update suite :passed inc)
        (do
          (update suite :failed inc)
          (print "  FAIL: " msg " (expected error containing '" expected-msg "', got '" actual-msg "')")))
      (do
        (update suite :failed inc)
        (print "  FAIL: " msg " (Expected error, but none thrown)")))
    threw))

(defn end-suite [&opt suite]
  (let [suite (or suite current-suite)
        passed (suite :passed)
        failed (suite :failed)
        total (+ passed failed)
        name (suite :name)]
    (print (string/format "  %d passed, %d failed" passed failed))
    (if (> failed 0)
      (do
        (print (string/format "test suite %s FAILED" name))
        (os/exit 1))
      (print (string/format "test suite %s passed (%d tests)" name total)))))
