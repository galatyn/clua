(ns clua.stdlib.vfs
  "VFS (virtual filesystem) utilities for CLua sandboxes.

   Use these functions when a script needs access to real files or directories.
   The sandbox must include :io (via make-sandbox or sandbox-full) before mounting.

   Typical usage:
     (require '[clua.core :as lua]
              '[clua.stdlib.core :as stdlib]
              '[clua.stdlib.vfs :as vfs])

     (vfs/with-sandbox [sb (vfs/mount (stdlib/make-sandbox #{:io})
                                      [{:type :file :real \"/data/in.csv\" :vfs \"in.csv\"}])]
       (lua/execute sb \"local f = assert(io.open('in.csv', 'r')) ...\"))"
  (:require [clojure.string :as str]
            [clua.interpreter.api :as interp]
            [clua.stdlib.io :as lua-io])
  (:import (java.io File)
           (java.nio.file Files StandardOpenOption)
           (java.nio.file OpenOption)))
(set! *warn-on-reflection* true)


;; ============================================================================
;; Private helpers
;; ============================================================================

(defn- sandbox-vfs
  "Extract the VFS atom from a sandbox, or nil if not present."
  [sandbox]
  (when-let [pkg (get sandbox "package")]
    (when (interp/lua-table? pkg)
      (let [vfs (interp/table-get pkg "vfs")]
        (when (instance? clojure.lang.Atom vfs)
          vfs)))))


;; ============================================================================
;; Public API
;; ============================================================================

(defn populate-vfs!
  "Register Lua source files in a sandbox's VFS so they can be require'd.

   sandbox   - sandbox with :io (from make-sandbox or sandbox-full)
   filenames - seq of bare filenames (e.g. [\"utils.lua\"]);
               stored under key \"./\" + filename to match the default
               package.path template \"./?.lua\"
   sources   - parallel seq of ISO-8859-1 source strings

   Returns sandbox unchanged."
  [sandbox filenames sources]
  (let [vfs (or (sandbox-vfs sandbox)
                (throw (ex-info "Sandbox has no VFS — use (make-sandbox #{:io ...}) or sandbox-full before populating VFS"
                                {:sandbox-keys (keys sandbox)})))]
    (doseq [[filename source] (map vector filenames sources)]
      (let [mf     (lua-io/make-memory-file)
            ^bytes bs (.getBytes ^String source "ISO-8859-1")]
        (lua-io/mf-write-bytes! mf 0 bs nil)
        (swap! vfs assoc (str "./" filename) mf))))
  sandbox)

(defn mount-file!
  "Mount a real file into the sandbox VFS so Lua scripts can access it via io.open.

   sandbox    - sandbox with :io (from make-sandbox or sandbox-full)
   real-path  - path to the real file on disk (String or java.io.File)
   vfs-path   - the path the Lua script uses (e.g. \"data.csv\" or \"/input/data.csv\")
   opts       - optional map:
                  :read-only? (default true)  - if false, writes go through to the real file

   Returns sandbox unchanged.

   Example:
     (mount-file! sb \"/real/path/data.csv\" \"data.csv\")
     ; Lua: local f = io.open(\"data.csv\", \"r\")"
  ([sandbox real-path vfs-path]
   (mount-file! sandbox real-path vfs-path {}))
  ([sandbox real-path vfs-path opts]
   (let [vfs (or (sandbox-vfs sandbox)
                 (throw (ex-info "Sandbox has no VFS — use (make-sandbox #{:io ...}) or sandbox-full before mounting files"
                                 {:sandbox-keys (keys sandbox)})))]
     (let [read-only? (get opts :read-only? true)
           backing    (lua-io/make-real-file-backing real-path read-only?)]
       (swap! vfs assoc (str vfs-path) backing)))
   sandbox))

(defn mount-dir!
  "Mount all files in a real directory into the sandbox VFS (recursive).

   sandbox      - sandbox with :io (from make-sandbox or sandbox-full)
   real-dir     - path to the real directory on disk (String or java.io.File)
   vfs-prefix   - VFS path prefix to mount under (e.g. \"inputs/\" or \"/data/\")
   opts         - optional map:
                    :read-only? (default true)
                    :recursive? (default true)

   Each file is mounted as: vfs-prefix + relative-path-within-dir
   Example: real-dir \"/data/\", file \"/data/a/b.csv\", prefix \"inputs/\"
            -> VFS path \"inputs/a/b.csv\"

   Returns sandbox unchanged."
  ([sandbox real-dir vfs-prefix]
   (mount-dir! sandbox real-dir vfs-prefix {}))
  ([sandbox real-dir vfs-prefix opts]
   (let [vfs        (or (sandbox-vfs sandbox)
                        (throw (ex-info "Sandbox has no VFS — use (make-sandbox #{:io ...}) or sandbox-full before mounting files"
                                        {:sandbox-keys (keys sandbox)})))
         read-only? (get opts :read-only? true)
         recursive? (get opts :recursive? true)
         dir        (File. (str real-dir))
         dir-path   (.getCanonicalPath dir)
         prefix     (str vfs-prefix)]
     (letfn [(mount-tree! [^File f]
               (if (.isDirectory f)
                 (when recursive?
                   (doseq [child (.listFiles f)]
                     (mount-tree! child)))
                 (let [file-path (.getCanonicalPath f)
                       rel-path  (subs file-path (count dir-path))
                       rel-clean (-> rel-path
                                     (str/replace "\\" "/")
                                     (str/replace #"^/" ""))
                       vfs-key   (str prefix rel-clean)
                       backing   (lua-io/make-real-file-backing f read-only?)]
                   (swap! vfs assoc vfs-key backing))))]
       (mount-tree! dir)))
   sandbox))

(defn flush-vfs!
  "Write modified/created VFS entries whose keys start with vfs-prefix back to real-dir.

   Only entries backed by MemoryFile are flushed (RealFileBacking writes go through
   immediately). Creates parent directories as needed.

   sandbox    - sandbox with :io (from make-sandbox or sandbox-full)
   vfs-prefix - only flush keys with this prefix (e.g. \"outputs/\" or \"/out/\")
   real-dir   - destination directory on disk

   Returns a seq of flushed VFS paths, or nil if sandbox has no VFS."
  [sandbox vfs-prefix real-dir]
  (when-let [vfs (sandbox-vfs sandbox)]
    (let [prefix   (str vfs-prefix)
          dest-dir (File. (str real-dir))
          flushed  (volatile! [])]
      (doseq [[vfs-path backing] @vfs
              :when (str/starts-with? vfs-path prefix)
              :when (lua-io/memory-file? backing)]
        (let [rel-path  (subs vfs-path (count prefix))
              dest-file (File. dest-dir rel-path)]
          (.mkdirs (.getParentFile dest-file))
          (let [content (lua-io/fb-read-all-string backing)
                ^bytes bs (.getBytes ^String content "ISO-8859-1")]
            (Files/write (.toPath dest-file) bs
                         ^"[Ljava.nio.file.OpenOption;"
                         (into-array OpenOption
                                     [StandardOpenOption/CREATE
                                      StandardOpenOption/TRUNCATE_EXISTING])))
          (vswap! flushed conj vfs-path)))
      @flushed)))

(defn- close-vfs-backings!
  "Close all RealFileBacking entries in the sandbox VFS, releasing file handles."
  [sandbox]
  (when-let [vfs (sandbox-vfs sandbox)]
    (doseq [[_path backing] @vfs
            :when (lua-io/real-file-backing? backing)]
      (lua-io/fb-close! backing)))
  sandbox)

(defn mount
  "Mount files/directories into a sandbox VFS. Returns sandbox unchanged.

   sandbox must include :io (from make-sandbox or sandbox-full).

   specs - vector of mount spec maps. Each map must have:
     :type       - :file or :dir
     :real       - real path on disk (String)
     :vfs        - path the Lua script uses (String)
     :read-only? - (optional, default true) false allows write-through to real file
     :recursive? - (optional, :dir only, default true) whether to recurse into subdirs

   Example:
     (mount (stdlib/make-sandbox #{:io})
            [{:type :file :real \"/data/input.csv\" :vfs \"input.csv\"}
             {:type :dir  :real \"/data/inputs\"    :vfs \"inputs/\" :recursive? false}
             {:type :file :real \"/tmp/out.txt\"    :vfs \"out.txt\" :read-only? false}])"
  [sandbox specs]
  (doseq [{:keys [type real vfs read-only? recursive?]
           :or   {read-only? true recursive? true}} specs]
    (case type
      :file (mount-file! sandbox real vfs {:read-only? read-only?})
      :dir  (mount-dir!  sandbox real vfs {:read-only? read-only? :recursive? recursive?})
      (throw (ex-info (str "Unknown mount type: " type) {:type type :real real :vfs vfs}))))
  sandbox)

(defmacro with-sandbox
  "Bind sandbox to sym, execute body, then close all VFS file handles.
   Guarantees cleanup even if body throws.

   Example:
     (vfs/with-sandbox [sb (vfs/mount (stdlib/make-sandbox #{:io})
                                      [{:type :file :real \"/data/in.csv\" :vfs \"in.csv\"}])]
       (lua/execute sb \"...\"))"
  [[sym sandbox-expr] & body]
  `(let [~sym ~sandbox-expr]
     (try
       ~@body
       (finally
         (close-vfs-backings! ~sym)))))
