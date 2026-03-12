(import ../../build/timer :as timer)
(import ../Utils/TestRunner :as test)

(def suite (test/start-suite "Native Timer"))

# Basic readings

(def before (timer/now))
(def after (timer/now))
(def before-ms (timer/ms))
(def after-ms (timer/ms))

(test/assert suite (<= before after) "timer/now is monotonic")
(test/assert suite (<= before-ms after-ms) "timer/ms is monotonic")

# Metadata reporting

(test/assert suite (= (timer/clock) "monotonic") "timer/clock reports monotonic clock")
(test/assert suite (= (timer/type) "s64") "Default timer type matches timer/now")
(test/assert suite (= (timer/type "now") "s64") "Now type query reports exact integer type")
(test/assert suite (= (timer/type "ms") "number") "Milliseconds type query reports Janet number")

(test/assert suite (= (timer/unit) "ns") "Default timer unit reports nanoseconds")
(test/assert suite (= (timer/unit "now") "ns") "Now unit query reports nanoseconds")
(test/assert suite (= (timer/unit "ms") "ms") "Milliseconds unit query reports milliseconds")

# Guard rails

(test/assert-error suite
  (fn [] (timer/type "bogus"))
  "Invalid timer/type query throws"
  "unsupported type query")

(test/assert-error suite
  (fn [] (timer/type "clock"))
  "Clock metadata moved to timer/clock"
  "unsupported type query")

(test/assert-error suite
  (fn [] (timer/unit "clock"))
  "Invalid timer/unit query throws"
  "unsupported unit query")

(test/end-suite suite)
