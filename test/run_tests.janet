#!/usr/bin/env janet

# Test runner for Requiem test suite
# Usage:
#   janet test/run_tests.janet          # Run all tests (excluding benchmarks)
#   janet test/run_tests.janet Identity # Run only tests matching "Identity"
#   janet test/run_tests.janet --bench  # Include benchmarks


# Get the directory where this script lives
(def script-path (dyn *current-file*))

(defn dirname [p]
  (def parts (string/split "/" p))
  (string/join (array/slice parts 0 -2) "/"))

(defn join-path [p1 p2]
  (string p1 "/" p2))

(def test-dir (dirname script-path))

(def test-subdirs ["Core" "Types" "Properties" "Equality" "Regression"])

(defn find-janet-files [subdir]
  "Find all .janet files in a subdirectory of test/"
  (def full-dir (join-path test-dir subdir))
  (if (os/stat full-dir)
    (seq [f :in (os/dir full-dir)
          :when (string/has-suffix? ".janet" f)]
      (join-path full-dir f))
    @[]))

(defn run-test-file [filepath]
  "Run a single test file and return true if it passed"
  (print)
  (print (string/repeat "-" 40))
  (print "Running " filepath)
  (print (string/repeat "-" 40))
  (try
    (do (dofile filepath) true)
    ([err]
      (print "FAILED: " filepath)
      (print "Error: " err)
      false)))

(def args (dyn *args*))
(def filter-str (get args 1 ""))
(def run-bench (= filter-str "--bench"))
(def filter-str (if run-bench "" filter-str))

(print "Discovering tests...")

(def dirs (if run-bench
            (array/concat (array ;test-subdirs) "Benchmarks")
            test-subdirs))

(var passed 0)
(var failed 0)

(each subdir dirs
  (each file (find-janet-files subdir)
    (when (or (empty? filter-str) (string/find filter-str file))
      (if (run-test-file file)
        (++ passed)
        (++ failed)))))

(print)
(print (string/repeat "=" 40))
(printf "SUMMARY: %d suites passed, %d failed" passed failed)
(print (string/repeat "=" 40))

(when (> failed 0)
  (os/exit 1))
