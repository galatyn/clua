(ns clua.stdlib.io
  "Lua 5.3 io library - virtual filesystem for sandboxed execution.

   File handles are Clojure maps with :clua-metatable for method dispatch.
   Virtual filesystem: atom mapping path-string -> IFileBacking.
   Two backing implementations:
     MemoryFile      - growable in-memory byte array (default)
     RealFileBacking - delegates directly to a java.io.RandomAccessFile"
  (:require [clojure.string :as str]
            [clua.interpreter.env :as env]
            [clua.interpreter.tables :as tables])
  (:import (java.io ByteArrayOutputStream RandomAccessFile)
           (java.util Arrays)))

(set! *warn-on-reflection* true)

;; ===========================================================================
;; IFileBacking protocol
;; ===========================================================================

(defprotocol IFileBacking
  (fb-size       [b]            "Return current size in bytes as long.")
  (fb-read-only? [b]            "Return true if the backing is read-only.")
  (fb-read-bytes [b pos n]      "Read n bytes at pos. Returns byte[], shorter at EOF, nil if pos>=size.")
  (fb-write!     [b pos data env] "Write byte[] data at pos, tracking allocation against env.")
  (fb-truncate!  [b]            "Truncate to zero bytes.")
  (fb-close!     [b]            "Release any underlying resource."))

(defn fb-read-all-string
  "Read the entire backing content as an ISO-8859-1 string."
  [b]
  (let [size (fb-size b)]
    (if (zero? size)
      ""
      (String. ^bytes (fb-read-bytes b 0 size) "ISO-8859-1"))))

;; ===========================================================================
;; MemoryFile - growable byte array
;; ===========================================================================

(deftype MemoryFile [^clojure.lang.Atom data-atom
                     ^clojure.lang.Atom size-atom])

(extend-type MemoryFile
  IFileBacking
  (fb-size [b]
    (long @(.size-atom b)))
  (fb-read-only? [_b] false)
  (fb-read-bytes [b pos n]
    (let [^bytes data @(.data-atom b)
          size (long @(.size-atom b))
          start (long pos)]
      (when (< start size)
        (let [end (min size (+ start (long n)))]
          (Arrays/copyOfRange data (int start) (int end))))))
  (fb-write! [b pos data env]
    (let [^bytes new-bytes data
          write-len (alength new-bytes)
          new-end (+ (long pos) write-len)]
      (swap! (.data-atom b)
             (fn [^bytes arr]
               (let [cap (alength arr)]
                 (if (> new-end cap)
                   (let [new-cap (max (* cap 2) (int new-end))
                         nd (byte-array new-cap)]
                     (System/arraycopy arr 0 nd 0 (alength arr))
                     (System/arraycopy new-bytes 0 nd (int pos) write-len)
                     nd)
                   (do (System/arraycopy new-bytes 0 arr (int pos) write-len)
                       arr)))))
      (swap! (.size-atom b) (fn [s] (max (long s) new-end)))
      (when env (env/track-allocation! env write-len))
      nil))
  (fb-truncate! [b]
    (reset! (.data-atom b) (byte-array 64))
    (reset! (.size-atom b) 0))
  (fb-close! [_b] nil))

(defn make-memory-file
  "Create a new empty MemoryFile."
  []
  (MemoryFile. (atom (byte-array 64)) (atom 0)))

;; Kept for callers in core.clj (populate-vfs! etc.)
(defn mf-write-bytes!
  "Write bytes into mf at pos."
  [^MemoryFile mf ^long pos ^bytes new-bytes cur-env]
  (fb-write! mf pos new-bytes cur-env))

(defn mf-get-string
  "Return the entire content of mf as an ISO-8859-1 string.
   Prefer fb-read-all-string for generic IFileBacking."
  [^MemoryFile mf]
  (fb-read-all-string mf))

;; ===========================================================================
;; RealFileBacking - delegates to RandomAccessFile
;; ===========================================================================

(deftype RealFileBacking [^RandomAccessFile raf
                          ^boolean read-only])

(extend-type RealFileBacking
  IFileBacking
  (fb-size [b]
    (.length ^RandomAccessFile (.raf b)))
  (fb-read-only? [b]
    (.read-only b))
  (fb-read-bytes [b pos n]
    (let [^RandomAccessFile raf (.raf b)
          size (.length raf)
          start (long pos)]
      (when (< start size)
        (let [actual (int (min (long n) (- size start)))
              buf (byte-array actual)]
          (.seek raf start)
          (.readFully raf buf 0 actual)
          buf))))
  (fb-write! [b pos data _env]
    (let [^RandomAccessFile raf (.raf b)
          ^bytes bs data]
      (.seek raf (long pos))
      (.write raf bs 0 (alength bs))
      nil))
  (fb-truncate! [b]
    (.setLength ^RandomAccessFile (.raf b) 0))
  (fb-close! [b]
    (.close ^RandomAccessFile (.raf b))))

(defn make-real-file-backing
  "Open a RealFileBacking on path (String or File).
   read-only? true uses mode 'r'; false uses 'rw'."
  [path read-only?]
  (RealFileBacking. (RandomAccessFile. (str path) (if read-only? "r" "rw"))
                    (boolean read-only?)))

(defn memory-file?
  "Return true if backing is an in-memory MemoryFile (not a real-file backing)."
  [b]
  (instance? MemoryFile b))

(defn real-file-backing?
  "Return true if backing delegates to a real file on disk."
  [b]
  (instance? RealFileBacking b))

;; ===========================================================================
;; File handle - Clojure map with :clua-metatable for method dispatch
;; ===========================================================================

(def ^:private -fh-meta-atom (atom nil))
(def ^:private tmp-file-counter (atom 0))

(defn- get-file-metatable [] @-fh-meta-atom)

(defn make-file-handle
  "Create a regular file handle for backing (IFileBacking) with the given mode and path."
  [backing mode path-str]
  (let [mode-ch (first (str mode))
        readable? (or (= mode-ch \r) (str/includes? (str mode) "+"))
        writable? (or (not= mode-ch \r) (str/includes? (str mode) "+"))
        append? (= mode-ch \a)
        init-pos (if append? (fb-size backing) 0)]
    {:type :file-handle
     :backing backing
     :pos-atom (atom init-pos)
     :readable? readable?
     :writable? writable?
     :append? append?
     :closed-atom (atom false)
     :standard? false
     :stdout? false
     :path-str path-str
     ;; PUC-Lua default: fully buffered for regular files (matches C stdio _IOFBF)
     :buf-state (atom {:mode "full"
                       :size 8192
                       :baos (ByteArrayOutputStream.)})
     :clua-metatable (get-file-metatable)}))

(defn make-stdout-handle
  "Virtual stdout/stderr handle - writes go to stdlib/*output-fn* (or System/out)."
  []
  {:type :file-handle
   :stdout? true
   :readable? false
   :writable? true
   :append? false
   :closed-atom (atom false)
   :standard? true
   :path-str "<stdout>"
   :clua-metatable (get-file-metatable)})

(defn make-null-output-handle
  "Discarding output handle — writes are silently dropped, nothing is stored.
   Used for stdout/stderr in restricted sandboxes so output cannot reach the
   real system and no memory is allocated to accumulate discarded bytes.
   standard? defaults to true (for stdin/stdout/stderr); pass false for
   user-opened /dev/null handles which should be closeable."
  ([path-str] (make-null-output-handle path-str true))
  ([path-str standard?]
   {:type :file-handle
    :null-device? true
    :readable? false
    :writable? true
    :closed-atom (atom false)
    :standard? standard?
    :path-str path-str
    :clua-metatable (get-file-metatable)}))

(defn make-stdin-handle
  "Virtual stdin handle - always empty (no input in sandbox)."
  []
  {:type :file-handle
   :backing (make-memory-file)
   :pos-atom (atom 0)
   :readable? true
   :writable? false
   :append? false
   :closed-atom (atom false)
   :standard? true
   :stdout? false
   :path-str "<stdin>"
   :clua-metatable (get-file-metatable)})

;; ===========================================================================
;; File type predicate
;; ===========================================================================

(defn file-type
  "Return 'file', 'closed file', or false (not a file handle)."
  [x]
  (cond
    (not (and (map? x) (= :file-handle (:type x)))) false
    @(:closed-atom x) "closed file"
    :else "file"))

;; ===========================================================================
;; Write
;; ===========================================================================

(defn- write-to-stdout
  "Write a byte string to stdout, using clua.stdlib/*output-fn* when bound."
  [^String s]
  (let [output-var (resolve 'clua.stdlib/*output-fn*)
        f (when output-var (var-get output-var))]
    (if f
      (f s)
      (do (.write System/out (.getBytes s "ISO-8859-1"))
          (.flush System/out)))))

(defn- strip-g-zeros
  "Strip trailing zeros from a Java %g-formatted number string."
  [^String s]
  (let [n (.length s)
        e-pos (loop [i 0]
                (cond (>= i n) nil
                      (let [c (.charAt s i)] (or (= c \e) (= c \E))) i
                      :else (recur (inc i))))
        has-decimal? (fn [^String m]
                       (loop [i (if (and (pos? (.length m))
                                         (let [c (.charAt m 0)]
                                           (or (= c \-) (= c \+)))) 1 0)]
                         (cond (>= i (.length m)) false
                               (not (Character/isDigit (.charAt m i))) true
                               :else (recur (inc i)))))
        strip (fn [^String m]
                (if-not (has-decimal? m)
                  m
                  (let [m2 (str/replace m #"0+$" "")]
                    (if (and (pos? (.length m2))
                             (not (Character/isDigit (.charAt m2 (dec (.length m2))))))
                      (subs m2 0 (dec (.length m2)))
                      m2))))]
    (if e-pos
      (str (strip (subs s 0 e-pos)) (subs s e-pos))
      (strip s))))

(defn- num->str
  "Convert a Lua number to a string for io.write."
  [n]
  (if (integer? n)
    (str n)
    (let [d (double n)
          loc (env/get-numeric-locale env/*current-env*)
          dec-char (env/numeric-decimal-char env/*current-env*)
          s14 (strip-g-zeros (String/format loc "%.14g" (into-array Object [d])))
          parsed (try (Double/parseDouble (str/replace s14 (str dec-char) "."))
                      (catch NumberFormatException _ nil))
          s (if (and parsed (== (double parsed) d))
              s14
              (strip-g-zeros (String/format loc "%.17g" (into-array Object [d]))))]
      (if (or (str/includes? s (str dec-char)) (re-find #"[eEnN]" s))
        s
        (str s dec-char "0")))))

(defn- write-bytes-to-backing!
  "Commit a byte array directly to fh's backing at current position."
  [fh ^bytes bs]
  (let [backing (:backing fh)
        pos-atom (:pos-atom fh)
        pos (if (:append? fh) (fb-size backing) (long @pos-atom))]
    (fb-write! backing pos bs env/*current-env*)
    (when-not (:append? fh)
      (swap! pos-atom + (alength bs)))))

(defn flush-buffer!
  "Flush any pending buffered bytes to backing. No-op for unbuffered handles.
   For /dev/full handles, clears the buffer and returns [nil errmsg errnum]."
  [fh]
  (if (:flush-fails? fh)
    (do (when-let [state-atom (:buf-state fh)]
          (.reset ^ByteArrayOutputStream (:baos @state-atom)))
        [nil "No space left on device" 28])
    (when-let [state-atom (:buf-state fh)]
      (let [^ByteArrayOutputStream baos (:baos @state-atom)]
        (when (pos? (.size baos))
          (write-bytes-to-backing! fh (.toByteArray baos))
          (.reset baos))))))

(defn file-write!
  "Write args to fh. Returns fh on success. Caller must check mode."
  [fh args]
  (when-not (:null-device? fh)
    (doseq [arg args]
      (let [s (cond
                (string? arg) arg
                (number? arg) (num->str arg)
                :else
                (throw (ex-info
                         (str "bad argument to 'write' (string expected, got "
                              (tables/lua-type-name arg) ")")
                         {:type :error})))]
        (if (:stdout? fh)
          (write-to-stdout s)
          (let [^bytes bs (.getBytes ^String s "ISO-8859-1")]
            (if-let [state-atom (:buf-state fh)]
              (let [{:keys [mode size ^ByteArrayOutputStream baos]} @state-atom]
                (case mode
                  "no"
                  (write-bytes-to-backing! fh bs)

                  "full"
                  (do (.write baos bs 0 (alength bs))
                      (when (>= (.size baos) (long size))
                        (flush-buffer! fh)))

                  "line"
                  (do (.write baos bs 0 (alength bs))
                      (when (loop [i 0]
                              (cond (>= i (alength bs)) false
                                    (= (aget bs i) (byte \newline)) true
                                    :else (recur (inc i))))
                        (flush-buffer! fh)))))
              (write-bytes-to-backing! fh bs)))))))
  fh)

;; ===========================================================================
;; Read helpers
;; ===========================================================================

(defn- read-line-bytes
  "Read one line from backing starting at pos. Returns [^bytes line-bytes new-pos].
   Strips \\r\\n or \\n. If keep-newline? is true, includes the \\n.
   Returns [nil pos] at EOF."
  [backing ^long pos keep-newline?]
  (let [size (fb-size backing)]
    (if (>= pos size)
      [nil pos]
      (let [baos (ByteArrayOutputStream. 256)]
        (loop [cur pos]
          (let [avail (- size cur)]
            (if (<= avail 0)
              ;; EOF without finding newline
              [(.toByteArray baos) cur]
              (let [n (min 8192 avail)
                    ^bytes chunk (fb-read-bytes backing cur n)
                    chunk-len (alength chunk)
                    nl-pos (loop [i 0]
                             (cond (>= i chunk-len) -1
                                   (= (aget chunk i) (byte \newline)) i
                                   :else (recur (inc i))))]
                (if (neg? nl-pos)
                  (do (.write baos chunk 0 chunk-len)
                      (recur (+ cur chunk-len)))
                  ;; Found \n at nl-pos
                  (let [_ (.write baos chunk 0 nl-pos)
                        full (.toByteArray baos)
                        flen (alength full)
                        ;; Strip trailing \r if present before the \n
                        strip (int (if (and (pos? flen)
                                            (= (aget full (dec flen)) (byte \return)))
                                     (dec flen)
                                     flen))
                        new-pos (+ cur nl-pos 1)]
                    [(if keep-newline?
                       (let [r (byte-array (inc strip))]
                         (System/arraycopy full 0 r 0 strip)
                         (aset r strip (byte \newline))
                         r)
                       (Arrays/copyOfRange full 0 strip))
                     new-pos]))))))))))

(defn- parse-num-str
  "Parse a number string (may be decimal int/float or hex int/float).
   Returns a Lua number or nil if the string is not a valid Lua number."
  [s]
  (when (pos? (count s))
    (try
      (if (re-find #"(?i)^[+-]?0x" s)
        (if (or (str/includes? (str/lower-case s) ".")
                (re-find #"(?i)p" s))
          (let [float-str (if (re-find #"(?i)p" s) s (str s "p0"))]
            (Double/parseDouble float-str))
          (let [neg? (str/starts-with? s "-")
                no-sign (if (or neg? (str/starts-with? s "+")) (subs s 1) s)
                hex-str (subs no-sign 2)]
            (when (pos? (count hex-str))
              (.longValue (if neg?
                            (.negate (BigInteger. hex-str 16))
                            (BigInteger. hex-str 16))))))
        (if (or (str/includes? s ".") (re-find #"(?i)e" s))
          (Double/parseDouble s)
          (try (Long/parseLong s)
               (catch NumberFormatException _
                 (Double/parseDouble s)))))
      (catch Exception _ nil))))

(defn- read-number-from
  "Read a number from backing at pos-atom, skipping leading whitespace.
   Mirrors PUC-Lua 5.3 liolib.c read_number exactly.
   Returns [number new-pos] on success or [nil new-pos] on failure."
  [backing pos-atom]
  (let [size (fb-size backing)
        start (long @pos-atom)]
    (if (>= start size)
      [nil start]
      ;; Read a bounded chunk - numbers are at most ~202 chars + leading whitespace.
      ;; 512 bytes is always sufficient.
      (let [chunk-n (min 512 (- size start))
            ^bytes data (fb-read-bytes backing start chunk-n)
            data-size (alength data)
            ;; Skip leading whitespace (local offset within data)
            ws-end (long (loop [i 0]
                           (if (and (< i data-size)
                                    (let [b (aget data i)]
                                      (or (= b 32) (= b 9) (= b 10) (= b 13) (= b 12) (= b 11))))
                             (recur (unchecked-inc i))
                             i)))]
        (if (>= ws-end data-size)
          [nil (+ start ws-end)]
          ;; Scanning state - pos-ref is a local offset within data
          (let [pos-ref (int-array [ws-end])
                buf (StringBuilder.)
                overflow (boolean-array [false])

                nextc (fn []
                        (cond
                          (aget overflow 0)
                          false
                          (>= (.length buf) 200)
                          (do (.setLength buf 0)
                              (aset overflow 0 true)
                              false)
                          :else
                          (let [p (aget pos-ref 0)]
                            (.append buf (char (bit-and (aget data p) 0xFF)))
                            (aset pos-ref 0 (inc p))
                            true)))

                rn-c (fn [] (let [p (aget pos-ref 0)]
                              (if (< p data-size) (char (bit-and (aget data p) 0xFF)) \u0000)))

                test2 (fn [c1 c2] (when (let [c (rn-c)] (or (= c c1) (= c c2))) (nextc)))

                readdigits (fn [hex?]
                             (loop [cnt (long 0)]
                               (let [c (rn-c)
                                     digit? (if hex?
                                              (>= (Character/digit ^char c 16) 0)
                                              (Character/isDigit ^char c))]
                                 (if (and digit? (nextc))
                                   (recur (unchecked-inc cnt))
                                   cnt))))]

            (test2 \- \+)

            (let [has0 (test2 \0 \0)
                  hex (when has0 (test2 \x \X))
                  base-count (long (if (and has0 (not hex)) 1 0))
                  count-int (long (readdigits (boolean hex)))
                  count (unchecked-add base-count count-int)
                  _ (test2 \. \.)
                  count-frac (long (readdigits (boolean hex)))
                  total (unchecked-add count count-frac)
                  _ (when (and (pos? total)
                               (test2 (if hex \p \e) (if hex \P \E)))
                      (test2 \- \+)
                      (readdigits false))
                  local-end (aget pos-ref 0)
                  buf-str (str buf)]
              (if (aget overflow 0)
                [nil (+ start local-end)]
                (let [n (parse-num-str buf-str)]
                  [n (+ start local-end)])))))))))

(defn read-one
  "Read a single value from backing according to format spec. Updates pos-atom.
   Returns the value (string, number, or nil at EOF).
   String formats: optional leading '*' stripped, then first char dispatched."
  [backing pos-atom fmt]
  (let [norm-fmt (if (string? fmt)
                   (let [s (if (str/starts-with? fmt "*") (subs fmt 1) fmt)]
                     (str (first s)))
                   fmt)]
    (cond
      (= norm-fmt "l")
      (let [[^bytes bs new-pos] (read-line-bytes backing @pos-atom false)]
        (reset! pos-atom new-pos)
        (when bs (String. bs "ISO-8859-1")))

      (= norm-fmt "L")
      (let [[^bytes bs new-pos] (read-line-bytes backing @pos-atom true)]
        (reset! pos-atom new-pos)
        (when bs (String. bs "ISO-8859-1")))

      (= norm-fmt "a")
      (let [size (fb-size backing)
            start (long @pos-atom)
            remaining (max 0 (- size start))]
        (reset! pos-atom size)
        (if (pos? remaining)
          (String. ^bytes (fb-read-bytes backing start remaining) "ISO-8859-1")
          ""))

      (= norm-fmt "n")
      (let [[num new-pos] (read-number-from backing pos-atom)]
        (reset! pos-atom new-pos)
        num)

      ;; read(0) - test for EOF: "" if data remains, nil if at EOF
      (and (number? fmt) (== (long fmt) 0))
      (if (>= (long @pos-atom) (fb-size backing)) nil "")

      ;; read(N) - read N bytes
      (and (number? fmt) (integer? fmt) (pos? (long fmt)))
      (let [pos (long @pos-atom)
            chunk (fb-read-bytes backing pos (long fmt))]
        (if (nil? chunk)
          nil
          (do (reset! pos-atom (+ pos (alength ^bytes chunk)))
              (String. ^bytes chunk "ISO-8859-1"))))

      :else
      (throw (ex-info (str "bad argument to 'read' (invalid format '" fmt "')")
                      {:type :error})))))

;; ===========================================================================
;; Lines iterator factory
;; ===========================================================================

(defn- make-lines-iter
  "Create a stateful line-reading iterator for fh.
   Supports multiple format specifiers. When close-on-eof? is true,
   the file is closed when the iterator returns nil."
  [fh fmts close-on-eof?]
  (let [actual-fmts (if (empty? fmts) ["l"] (vec fmts))]
    (fn [& _]
      (when @(:closed-atom fh)
        (throw (ex-info "file is already closed" {:type :error})))
      (when-not (:readable? fh)
        (throw (ex-info "file is not open for reading" {:type :error})))
      (let [backing (:backing fh)
            pos-atom (:pos-atom fh)
            results (mapv #(read-one backing pos-atom %) actual-fmts)
            first-val (first results)]
        (when (and (nil? first-val) close-on-eof? (not (:standard? fh)))
          (reset! (:closed-atom fh) true))
        (cond
          (nil? first-val) nil
          (= 1 (count results)) first-val
          :else (vec results))))))

(defn- make-dev-full-handle
  "Create a file handle for /dev/full: writes succeed, flush always fails."
  []
  {:type :file-handle
   :backing (make-memory-file)
   :pos-atom (atom 0)
   :readable? false
   :writable? true
   :append? false
   :closed-atom (atom false)
   :standard? false
   :stdout? false
   :path-str "/dev/full"
   :flush-fails? true
   :buf-state (atom {:mode "no" :size 8192 :baos (ByteArrayOutputStream.)})
   :clua-metatable (get-file-metatable)})

;; ===========================================================================
;; io.open
;; ===========================================================================

(defn- vfs-parent-exists?
  "Return true when the parent directory of path-str is reachable in the VFS."
  [vfs ^String path-str]
  (let [last-slash (.lastIndexOf path-str "/")]
    (if (<= last-slash 0)
      true
      (let [parent (subs path-str 0 (inc last-slash))]
        (or (= parent "/tmp/")
            (some #(str/starts-with? % parent) (keys @vfs)))))))

(defn lua-io-open
  "Open a file on the virtual filesystem.
   Returns a file handle on success, or [nil errmsg errnum] on failure."
  [vfs path mode]
  (let [mode-str (str (or mode "r"))
        mode-ch (first mode-str)
        path-str (str path)]
    (when-not (re-matches #"[rwa]\+?b?" mode-str)
      (throw (ex-info "bad argument #2 to 'open' (invalid mode)"
                      {:type :error})))
    (cond
      (= path-str "/dev/null")
      (if (= mode-ch \r)
        (make-file-handle (make-memory-file) mode-str path-str)
        (make-null-output-handle "/dev/null" false))

      (= path-str "/dev/full")
      (if (= mode-ch \r)
        [nil "/dev/full: Permission denied" 13]
        (make-dev-full-handle))

      :else
      (let [backing (get @vfs path-str)
            write-mode? (or (= mode-ch \w) (= mode-ch \a)
                            (str/includes? mode-str "+"))]
        (cond
          ;; Read mode: file must exist
          (= mode-ch \r)
          (if backing
            (make-file-handle backing mode-str path-str)
            [nil (str path-str ": No such file or directory") 2])

          ;; Write/append on a read-only backing: permission denied
          (and backing write-mode? (fb-read-only? backing))
          [nil (str path-str ": Permission denied") 13]

          ;; Write mode: create or truncate
          (= mode-ch \w)
          (if-not (vfs-parent-exists? vfs path-str)
            [nil (str path-str ": No such file or directory") 2]
            (let [new-backing (or backing (make-memory-file))]
              (fb-truncate! new-backing)
              (swap! vfs assoc path-str new-backing)
              (make-file-handle new-backing mode-str path-str)))

          ;; Append mode: create if not exists
          (= mode-ch \a)
          (if-not (vfs-parent-exists? vfs path-str)
            [nil (str path-str ": No such file or directory") 2]
            (let [new-backing (or backing (make-memory-file))]
              (swap! vfs assoc path-str new-backing)
              (make-file-handle new-backing mode-str path-str)))

          :else
          [nil (str "invalid mode: " mode-str) 22])))))

;; ===========================================================================
;; io table factory
;; ===========================================================================

(defn make-io-table
  "Create the Lua io library table backed by vfs.
   vfs is an (atom {}) mapping path-string -> IFileBacking.
   opts is an optional map:
     :real-stdout? - when true, stdout/stderr write to real System/out.
                     When false (default), they discard output silently.
   Returns a Lua table suitable for injection into the sandbox."
  ([vfs] (make-io-table vfs {}))
  ([vfs opts]
   (let [real-stdout? (:real-stdout? opts false)
        stdin (make-stdin-handle)
        stdout (if real-stdout? (make-stdout-handle) (make-null-output-handle "<stdout>"))
        stderr (if real-stdout? (make-stdout-handle) (make-null-output-handle "<stderr>"))
        cur-input-atom (atom stdin)
        cur-output-atom (atom stdout)
        io-table (tables/make-table)]

    ;; Standard streams
    (tables/table-set! io-table "stdin" stdin)
    (tables/table-set! io-table "stdout" stdout)
    (tables/table-set! io-table "stderr" stderr)

    ;; io.open
    (tables/table-set! io-table "open"
                       (fn [path & [mode]]
                         (lua-io-open vfs path mode)))

    ;; io.close
    (tables/table-set! io-table "close"
                       (fn [& [fh]]
                         (let [target (or fh @cur-output-atom)]
                           (cond
                             @(:closed-atom target)
                             (throw (ex-info "attempt to use a closed file" {:type :error}))
                             (:standard? target)
                             [nil "cannot close standard file"]
                             :else
                             (do (flush-buffer! target)
                                 (reset! (:closed-atom target) true)
                                 true)))))

    ;; io.type
    (tables/table-set! io-table "type"
                       (fn [x] (file-type x)))

    ;; io.input
    (tables/table-set! io-table "input"
                       (fn [& [arg]]
                         (cond
                           (nil? arg)
                           @cur-input-atom

                           (string? arg)
                           (let [fh (lua-io-open vfs arg "r")]
                             (when (vector? fh)
                               (throw (ex-info (str arg ": " (second fh)) {:type :error})))
                             (reset! cur-input-atom fh)
                             fh)

                           (and (map? arg) (= :file-handle (:type arg)))
                           (do (reset! cur-input-atom arg) arg)

                           :else (throw (ex-info (str "bad argument #1 to 'input' (FILE* expected, got "
                                                      (tables/lua-type-name arg) ")")
                                                 {:type :error})))))

    ;; io.output
    (tables/table-set! io-table "output"
                       (fn [& [arg]]
                         (cond
                           (nil? arg)
                           @cur-output-atom

                           (string? arg)
                           (let [_ (flush-buffer! @cur-output-atom)
                                 fh (lua-io-open vfs arg "w")]
                             (when (vector? fh)
                               (throw (ex-info (str arg ": " (second fh)) {:type :error})))
                             (reset! cur-output-atom fh)
                             fh)

                           (and (map? arg) (= :file-handle (:type arg)))
                           ;; Flush old output before switching away — approximates PUC-Lua's
                           ;; behaviour where the old handle is flushed/closed by __gc.
                           (do (flush-buffer! @cur-output-atom)
                               (reset! cur-output-atom arg)
                               arg)

                           :else (throw (ex-info "bad argument to 'output'" {:type :error})))))

    ;; io.read
    (tables/table-set! io-table "read"
                       (fn [& fmts]
                         (let [fh @cur-input-atom]
                           (when @(:closed-atom fh)
                             (throw (ex-info "standard input file is closed" {:type :error})))
                           (let [backing (:backing fh)
                                 pos-atom (:pos-atom fh)
                                 fmts (if (empty? fmts) ["l"] (vec fmts))]
                             (if (= 1 (count fmts))
                               (read-one backing pos-atom (first fmts))
                               (mapv #(read-one backing pos-atom %) fmts))))))

    ;; io.write
    (tables/table-set! io-table "write"
                       (fn [& args]
                         (let [fh @cur-output-atom]
                           (when @(:closed-atom fh)
                             (throw (ex-info "standard output file is closed" {:type :error})))
                           (file-write! fh args)
                           fh)))

    ;; io.flush
    (tables/table-set! io-table "flush"
                       (fn [] (let [fh @cur-output-atom] (or (flush-buffer! fh) fh))))

    ;; io.popen - not supported
    (tables/table-set! io-table "popen"
                       (fn [& _] [nil "io.popen not supported in sandbox" 1]))

    ;; io.tmpfile
    (tables/table-set! io-table "tmpfile"
                       (fn []
                         (let [path (str "/tmp/lua_io_" (swap! tmp-file-counter inc))
                               mf (make-memory-file)]
                           (swap! vfs assoc path mf)
                           (make-file-handle mf "r+" path))))

    ;; io.lines
    (tables/table-set! io-table "lines"
                       (fn [& args]
                         (let [path (first args)
                               fmts (rest args)]
                           (when (> (count fmts) 250)
                             (throw (ex-info "too many arguments to 'lines'" {:type :error})))
                           (cond
                             (nil? path)
                             (make-lines-iter @cur-input-atom fmts false)

                             (string? path)
                             (let [fh (lua-io-open vfs path "r")]
                               (when (vector? fh)
                                 (throw (ex-info (str path ": " (second fh)) {:type :error})))
                               [(make-lines-iter fh fmts true) nil nil fh])

                             :else (throw (ex-info "bad argument to 'lines'" {:type :error}))))))

    io-table)))

;; ===========================================================================
;; File handle methods table and metatable
;; ===========================================================================

(defn- make-methods-table
  "Build the Lua table of file handle methods."
  []
  (let [t (tables/make-table)]
    ;; f:read(...)
    (tables/table-set! t "read"
                       (fn [fh & fmts]
                         (cond
                           @(:closed-atom fh)
                           (throw (ex-info "file is already closed" {:type :error}))
                           (not (:readable? fh))
                           [nil "file is not open for reading" 9]
                           :else
                           (let [backing (:backing fh)
                                 pos-atom (:pos-atom fh)
                                 fmts (if (empty? fmts) ["l"] (vec fmts))]
                             (if (= 1 (count fmts))
                               (read-one backing pos-atom (first fmts))
                               (mapv #(read-one backing pos-atom %) fmts))))))

    ;; f:write(...)
    (tables/table-set! t "write"
                       (fn [fh & args]
                         (cond
                           @(:closed-atom fh)
                           (throw (ex-info "file is already closed" {:type :error}))
                           (not (:writable? fh))
                           [nil "file is not open for writing" 9]
                           :else
                           (file-write! fh args))))

    ;; f:seek([whence [, offset]])
    (tables/table-set! t "seek"
                       (fn [fh & args]
                         (when @(:closed-atom fh)
                           (throw (ex-info "file is already closed" {:type :error})))
                         (if (:stdout? fh)
                           [nil "seek on non-seekable file" 29]
                           ;; C stdio fseek always flushes the write buffer first.
                           ;; This ensures pos-atom is up to date before computing new-pos.
                           (let [flush-err (flush-buffer! fh)]
                             (if flush-err
                               flush-err
                               (let [whence (or (first args) "cur")
                                     offset (long (or (second args) 0))
                                     backing (:backing fh)
                                     size (fb-size backing)
                                     cur-pos (long @(:pos-atom fh))
                                     new-pos (case whence
                                               "set" offset
                                               "cur" (+ cur-pos offset)
                                               "end" (+ size offset)
                                               nil)]
                                 (cond
                                   (nil? new-pos)
                                   [nil (str "bad argument #1 to 'seek' (invalid option '" whence "')") 22]
                                   (neg? (long new-pos))
                                   [nil "invalid file position" 22]
                                   :else
                                   (do (reset! (:pos-atom fh) new-pos)
                                       new-pos))))))))

    ;; f:setvbuf(mode [, size])
    (tables/table-set! t "setvbuf"
                       (fn [fh mode & [size]]
                         (when-let [state-atom (:buf-state fh)]
                           (flush-buffer! fh)
                           (swap! state-atom assoc
                                  :mode (str mode)
                                  :size (if (and size (pos? (long size))) (long size) 8192)))
                         true))

    ;; f:close()
    (tables/table-set! t "close"
                       (fn [& args]
                         (let [fh (first args)]
                           (when-not fh
                             (throw (ex-info "bad argument #1 to 'close' (file expected, got no value)"
                                             {:type :error})))
                           (if (:standard? fh)
                             [nil "cannot close standard file"]
                             (do (flush-buffer! fh)
                                 (when-let [b (:backing fh)]
                                   (fb-close! b))
                                 (reset! (:closed-atom fh) true)
                                 true)))))

    ;; f:lines([fmt...])
    (tables/table-set! t "lines"
                       (fn [fh & fmts]
                         (when (> (count fmts) 250)
                           (throw (ex-info "too many arguments to 'lines'" {:type :error})))
                         (make-lines-iter fh fmts false)))

    ;; f:flush()
    (tables/table-set! t "flush"
                       (fn [fh] (or (flush-buffer! fh) fh)))

    t))

(defn- make-file-metatable
  "Build the metatable for file handles (__name, __index, __tostring, __gc, __close)."
  [methods-table]
  (let [mt (tables/make-table)]
    (tables/table-set! mt "__name" "FILE*")
    (tables/table-set! mt "__index" methods-table)
    (tables/table-set! mt "__tostring"
                       (fn [fh]
                         (if @(:closed-atom fh)
                           "file (closed)"
                           (str "file (0x" (Integer/toHexString (System/identityHashCode fh)) ")"))))
    (tables/table-set! mt "__gc"
                       (fn [& args]
                         (let [fh (first args)]
                           (when-not (and (map? fh) (:closed-atom fh))
                             (throw (ex-info "bad argument #1 to '__gc' (file expected, got no value)"
                                             {:type :error})))
                           (reset! (:closed-atom fh) true)
                           nil)))
    (tables/table-set! mt "__close"
                       (fn [fh & _]
                         (when (and (map? fh) (:closed-atom fh) (not @(:closed-atom fh)))
                           (when-not (:standard? fh)
                             (flush-buffer! fh)
                             (when-let [b (:backing fh)]
                               (fb-close! b))
                             (reset! (:closed-atom fh) true)))
                         nil))
    mt))

;; Initialize metatable and methods table when namespace is loaded
(let [methods (make-methods-table)
      mt (make-file-metatable methods)]
  (reset! -fh-meta-atom mt))
