#!/usr/bin/env janet

(import ./src/parser :as p)
(import ./src/lower :as l)
(import ./src/elab :as e)
(import ./src/coreTT :as c)

# Configuration
(def version "0.1.0")
(def requiem-name "requiem")

# Utility functions
(defn usage []
  (print (string requiem-name " " version))
  (print "Usage: " requiem-name " <flag> <filename>")
  (print "")
  (print "Available flags:")
  (print "  -h, --help       Show this help message")
  (print "  -v, --version    Show version information")
  (print "  -t, --typecheck  Type check a file")
  (print "  -c, --compile    Compile to core representation")
  (print "  -r, --run        Parse, type check and run (default)")
  (print "  -p, --parse      Parse and show AST")
  (print "  -l, --lower      Parse and lower to declarations")
  (print "  -e, --elab       Parse, lower and elaborate")
  (print "  -n, --norm       Normalize terms")
  (print "  --render         Parse and render formatted output")
  (print "")
  (print "Examples:")
  (print "  " requiem-name " --typecheck file.requiem")
  (print "  " requiem-name " --compile file.requiem")
  (print "  " requiem-name " --run file.requiem")
  (print "  " requiem-name " --parse file.requiem"))

(defn error/exit [msg &opt code]
  (eprint msg)
  (os/exit (or code 1)))

(defn file/exists? [path]
  (try
    (do (file/open path :r)
        true)
    ([_] false)))

(defn validate/file [path]
  (unless (file/exists? path)
    (error/exit (string "Error: file not found: " path)))
  (unless (or (string/has-suffix? ".requiem" path)
              (string/has-suffix? ".req" path))
    (print "Warning: file does not have .requiem or .req extension")))

# Task implementations
(defn decl/summary [decl]
  (match decl
    [:decl/data name _ _ ctors]
    (string "data " name " (" (length ctors) " constructor(s))")
    [:decl/func name params _ clauses]
    (string "def " name " (" (length params) " param(s), " (length clauses) " clause(s))")
    _
    (string "unknown declaration: " decl)))

(defn parse/file [path verbose]
  (when verbose (print "Parsing " path "..."))
  (def src (slurp path))
  (def forms (p/parse/text src))
  (when verbose (print "Parsed " (length forms) " interaction(s)"))
  forms)

(defn lower/file [path verbose]
  (def forms (parse/file path verbose))
  (when verbose (print "Lowering declarations..."))
  (def lowered (l/lower/program forms))
  (when verbose (print "Lowered " (length lowered) " declaration(s)"))
  lowered)

(defn elab/file [path verbose]
  (def lowered (lower/file path verbose))
  (when verbose (print "Elaborating core declarations..."))
  (def core (e/elab/program lowered))
  (when verbose (print "Elaborated " (length core) " core declaration(s)"))
  core)

(defn typecheck/file [path verbose]
  (try
    (do
      (def core (elab/file path verbose))
      (when verbose (print "Type checking..."))
      # Type checking happens during elaboration
      (print "✓ " path " type checks successfully")
      (print "  " (length core) " declaration(s) processed"))
    ([err] (error/exit (string "Type error: " err)))))

(defn compile/file [path verbose]
  (def core (elab/file path verbose))
  (print "Compiled " path " to core representation:")
  (each decl core
    (print "  " decl)))

(defn run/file [path verbose]
  (def start (os/clock))
  (def src (slurp path))
  (when verbose (print "Parsing " path "..."))
  (def forms (p/parse/text src))
  (def interactions (length forms))
  (when verbose (print "Parsed " interactions " interaction(s)"))
  (def lowered (l/lower/program forms))
  (when verbose 
    (print "Lowered declarations: " (length lowered))
    (each decl lowered
      (print "  - " (decl/summary decl))))
  (def core (e/elab/program lowered))
  (when verbose (print "Elaborated core declarations: " (length core)))
  (def elapsed (- (os/clock) start))
  (printf "Done. %d interaction(s) in %.3fs" interactions elapsed))

(defn norm/file [path verbose]
  (def core (elab/file path verbose))
  (when verbose (print "Normalizing terms..."))
  # For now, just show that we have the core terms
  # TODO: Implement actual normalization of individual terms
  (print "Normalization not yet implemented for full files")
  (print "Core terms available: " (length core)))

(defn render/file [path verbose]
  (def forms (parse/file path verbose))
  (when verbose (print "Rendering formatted output..."))
  (def rendered (p/render/program forms))
  (print rendered))

# Command-line parsing
(defn parse/args [args]
  (def len (length args))
  (cond
    (zero? len) nil # No args
    (= len 1) 
      (let [arg (args 0)]
        (cond
          (or (= arg "-h") (= arg "--help")) :help
          (or (= arg "-v") (= arg "--version")) :version
          {:task :run :file arg}))
    (= len 2)
      (let [[flag file] args]
        (cond
          (or (= flag "-h") (= flag "--help")) :help
          (or (= flag "-v") (= flag "--version")) :version
          (or (= flag "-t") (= flag "--typecheck")) {:task :typecheck :file file}
          (or (= flag "-c") (= flag "--compile")) {:task :compile :file file}
          (or (= flag "-r") (= flag "--run")) {:task :run :file file}
          (or (= flag "-p") (= flag "--parse")) {:task :parse :file file}
          (or (= flag "-l") (= flag "--lower")) {:task :lower :file file}
          (or (= flag "-e") (= flag "--elab")) {:task :elab :file file}
          (or (= flag "-n") (= flag "--norm")) {:task :norm :file file}
          (= flag "--render") {:task :render :file file}
          (error/exit (string "Unknown flag: " flag))))
    (error/exit "Too many arguments. Use --help for usage information.")))

# Task dispatcher
(defn dispatch/task [task file verbose]
  (case task
    :typecheck (typecheck/file file verbose)
    :compile (compile/file file verbose)
    :run (run/file file verbose)
    :parse (parse/file file verbose)
    :lower (lower/file file verbose)
    :elab (elab/file file verbose)
    :norm (norm/file file verbose)
    :render (render/file file verbose)
    (error/exit (string "Unknown task: " task))))

# Main entry point
(defn main [& args]
  # Filter out the script name from args
  (def filtered-args (if (and (> (length args) 0) 
                              (string/has-suffix? "requiem.janet" (args 0)))
                       (array/slice args 1)
                       args))
  (def parsed (parse/args filtered-args))
  (case parsed
    :help (usage)
    :version (print requiem-name " " version)
    nil (usage)
    (let [{:task task :file file} parsed]
      (validate/file file)
      (dispatch/task task file true))))
