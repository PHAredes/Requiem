#!/usr/bin/env janet

(def warnings @{})

(defn warn! [key message]
  (when (nil? (get warnings key))
    (put warnings key true)
    (eprintf "warning: %s\n" message)))

(def exports
  {:warn! warn!})
