(ns clua.stdlib.utf8
  "Lua utf8 library implementation.

   Implements Lua 5.3 basic UTF-8 support functions.

   CLua string model: byte sequences stored as Java chars 0–255 (one char per byte).
   Non-ASCII source chars are re-encoded to UTF-8 bytes during parsing.
   This matches real Lua 5.3 byte semantics exactly.

   UTF-8 validity rules (per Lua 5.3 / RFC 3629):
   - 0x00–0x7F:  1-byte sequence (ASCII, always valid)
   - 0xC2–0xDF:  2-byte lead  (0xC0–0xC1 are overlong = invalid)
   - 0xE0–0xEF:  3-byte lead
   - 0xF0–0xF4:  4-byte lead  (0xF5–0xFF = invalid)
   - 0x80–0xBF:  continuation byte (invalid as first byte)
   Overlong encodings and surrogate codepoints are also invalid.")
(set! *warn-on-reflection* true)


;; =============================================================================
;; Helper Functions
;; =============================================================================

(defn- utf8-seq-len
  "Given a lead byte (0–255), return sequence length 1–4, or nil if invalid (strict)."
  [^long b]
  (cond
    (<= b 0x7F) 1
    (and (>= b 0xC2) (<= b 0xDF)) 2
    (and (>= b 0xE0) (<= b 0xEF)) 3
    (and (>= b 0xF0) (<= b 0xF4)) 4
    :else nil))

(defn- utf8-seq-len-lax
  "Given a lead byte (0–255), return sequence length 1–6 for lax/nonstrict mode.
   Accepts 5-byte (0xF8–0xFB) and 6-byte (0xFC–0xFD) lead bytes."
  [^long b]
  (cond
    (<= b 0x7F) 1
    (and (>= b 0xC0) (<= b 0xDF)) 2
    (and (>= b 0xE0) (<= b 0xEF)) 3
    (and (>= b 0xF0) (<= b 0xF7)) 4
    (and (>= b 0xF8) (<= b 0xFB)) 5
    (and (>= b 0xFC) (<= b 0xFD)) 6
    :else nil))

(defn- continuation?
  "Returns true if b (0–255) is a UTF-8 continuation byte."
  [^long b]
  (and (>= b 0x80) (<= b 0xBF)))

(defn- decode-utf8
  "Decode one UTF-8 sequence starting at 1-based position pos in string s.
   Returns [codepoint seqlen] on success, or nil if the sequence is invalid.
   Validates: lead byte, continuation bytes, overlong, out-of-range, surrogates."
  [^String s ^long pos]
  (let [slen (long (.length s))
        lead (int (.charAt s (unchecked-dec pos)))
        seqlen (utf8-seq-len lead)]
    (when seqlen
      (let [seqlen (long seqlen)]
        (if (= seqlen 1)
          [lead 1]
          (when (<= (unchecked-add pos (unchecked-subtract seqlen 1)) slen)
            (let [b1 (int (.charAt s pos))                  ; 1-based pos+1 → 0-based pos
                  b2 (long (if (>= seqlen 3) (int (.charAt s (unchecked-inc pos))) 0))
                  b3 (long (if (>= seqlen 4) (int (.charAt s (unchecked-add pos 2))) 0))
                  valid-conts? (case seqlen
                                 2 (continuation? b1)
                                 3 (and (continuation? b1) (continuation? b2))
                                 4 (and (continuation? b1) (continuation? b2) (continuation? b3)))]
              (when valid-conts?
                (let [cp (case seqlen
                           2 (bit-or (bit-shift-left (bit-and lead 0x1F) 6)
                                     (bit-and b1 0x3F))
                           3 (bit-or (bit-shift-left (bit-and lead 0x0F) 12)
                                     (bit-shift-left (bit-and b1 0x3F) 6)
                                     (bit-and b2 0x3F))
                           4 (bit-or (bit-shift-left (bit-and lead 0x07) 18)
                                     (bit-shift-left (bit-and b1 0x3F) 12)
                                     (bit-shift-left (bit-and b2 0x3F) 6)
                                     (bit-and b3 0x3F)))
                      min-cp (case seqlen 2 0x80 3 0x800 4 0x10000)]
                  (when (and (>= cp min-cp)
                             (<= cp 0x10FFFF)
                             (not (and (>= cp 0xD800) (<= cp 0xDFFF))))
                    [cp seqlen]))))))))))

(defn- decode-utf8-lax
  "Lax/nonstrict UTF-8 decoder: handles 1–6 byte sequences, surrogates, and
   codepoints > 0x10FFFF (up to 0x7FFFFFFF). Returns [codepoint seqlen] or nil."
  [^String s ^long pos]
  (let [slen (long (.length s))
        lead (int (.charAt s (unchecked-dec pos)))
        seqlen (utf8-seq-len-lax lead)]
    (when seqlen
      (let [seqlen (long seqlen)]
        (if (= seqlen 1)
          [lead 1]
          (when (<= (unchecked-add pos (unchecked-subtract seqlen 1)) slen)
            (let [bs (mapv #(int (.charAt s (unchecked-add (unchecked-dec pos) (long %)))) (range 1 seqlen))
                  valid-conts? (every? continuation? bs)]
              (when valid-conts?
                (let [b0 (long (nth bs 0))
                      b1 (long (if (>= seqlen 3) (nth bs 1) 0))
                      b2 (long (if (>= seqlen 4) (nth bs 2) 0))
                      b3 (long (if (>= seqlen 5) (nth bs 3) 0))
                      b4 (long (if (>= seqlen 6) (nth bs 4) 0))
                      cp (case seqlen
                           2 (bit-or (bit-shift-left (bit-and lead 0x1F) 6)
                                     (bit-and b0 0x3F))
                           3 (bit-or (bit-shift-left (bit-and lead 0x0F) 12)
                                     (bit-shift-left (bit-and b0 0x3F) 6)
                                     (bit-and b1 0x3F))
                           4 (bit-or (bit-shift-left (bit-and lead 0x07) 18)
                                     (bit-shift-left (bit-and b0 0x3F) 12)
                                     (bit-shift-left (bit-and b1 0x3F) 6)
                                     (bit-and b2 0x3F))
                           5 (bit-or (bit-shift-left (bit-and lead 0x03) 24)
                                     (bit-shift-left (bit-and b0 0x3F) 18)
                                     (bit-shift-left (bit-and b1 0x3F) 12)
                                     (bit-shift-left (bit-and b2 0x3F) 6)
                                     (bit-and b3 0x3F))
                           6 (bit-or (bit-shift-left (bit-and lead 0x01) 30)
                                     (bit-shift-left (bit-and b0 0x3F) 24)
                                     (bit-shift-left (bit-and b1 0x3F) 18)
                                     (bit-shift-left (bit-and b2 0x3F) 12)
                                     (bit-shift-left (bit-and b3 0x3F) 6)
                                     (bit-and b4 0x3F)))]
                  (when (<= 0 cp 0x7FFFFFFF)
                    [cp seqlen]))))))))))

;; =============================================================================

;; UTF-8 Library Functions
;; =============================================================================

(defn lua-char
  "utf8.char(...)
   Receives zero or more integers, converts each one to its corresponding
   UTF-8 byte sequence, and returns a string with the concatenation.
   Accepts values 0–0x7FFFFFFF (Lua 5.4 extended range).
   Throws 'value out of range' for values outside that range."
  [& codepoints]
  (apply str (map (fn [cp]
                    (let [cp (long cp)]
                      (when (or (< cp 0) (> cp 0x7FFFFFFF))
                        (throw (ex-info "value out of range" {:type :error})))
                      (let [sb (StringBuilder.)]
                        (cond
                          (<= cp 0x10FFFF)
                          ;; Valid Unicode: use Java for correctness
                          (let [utf8-bytes (.getBytes (String. (Character/toChars (int cp))) "UTF-8")]
                            (doseq [b utf8-bytes]
                              (.append sb (char (Byte/toUnsignedInt b)))))
                          :else
                          ;; Extended range: manual encoding
                          (cond
                            (<= cp 0x1FFFFF)
                            (do (.append sb (char (bit-or 0xF0 (bit-shift-right cp 18))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 12) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 6) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and cp 0x3F)))))
                            (<= cp 0x3FFFFFF)
                            (do (.append sb (char (bit-or 0xF8 (bit-shift-right cp 24))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 18) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 12) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 6) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and cp 0x3F)))))
                            :else
                            (do (.append sb (char (bit-or 0xFC (bit-shift-right cp 30))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 24) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 18) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 12) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and (bit-shift-right cp 6) 0x3F))))
                                (.append sb (char (bit-or 0x80 (bit-and cp 0x3F)))))))
                        (str sb))))
                  codepoints)))

(defn lua-codes
  "utf8.codes(s [, lax])
   Returns an iterator function that yields (position, codepoint) pairs.
   lax=true enables nonstrict decoding.
   Throws 'invalid UTF-8 code' if an invalid byte is encountered."
  [^String s & [lax]]
  (let [slen (long (.length s))
        pos (atom 1)
        decode (if lax decode-utf8-lax decode-utf8)]
    (fn [& _]
      (let [p (long @pos)]
        (when (<= p slen)
          (let [result (decode s p)]
            (when (nil? result)
              (throw (ex-info "invalid UTF-8 code" {:type :error :position p})))
            (let [[cp seqlen] result]
              (swap! pos + seqlen)
              [p cp])))))))

(defn lua-codepoint
  "utf8.codepoint(s [, i [, j [, lax]]])
   Returns the codepoints from positions i through j (both inclusive).
   Default: i=1, j=i. lax=true enables nonstrict decoding (surrogates, > 0x10FFFF).
   Throws 'invalid UTF-8 code' for invalid byte sequences.
   Throws 'out of range' for out-of-bounds positions."
  [^String s & [i j lax]]
  (let [slen (long (.length s))
        i (long (or i 1))
        j-arg (if (nil? j) i (long j))
        i (long (if (neg? i) (+ slen i 1) i))
        j (long (if (neg? j-arg) (+ slen j-arg 1) j-arg))
        decode (if lax decode-utf8-lax decode-utf8)]
    (if (> i j)
      nil
      (do
        (when (or (< i 1) (> i (unchecked-inc slen)))
          (throw (ex-info "out of bounds" {:type :error})))
        (when (> j slen)
          (throw (ex-info "out of bounds" {:type :error})))
        (loop [pos i result []]
          (if (> pos j)
            (if (= 1 (count result)) (first result) (when (seq result) result))
            (let [decoded (decode s pos)]
              (when (nil? decoded)
                (throw (ex-info "invalid UTF-8 code" {:type :error :position pos})))
              (let [[cp seqlen] decoded]
                (recur (unchecked-add pos (long seqlen)) (conj result cp))))))))))

(defn lua-len
  "utf8.len(s [, i [, j [, lax]]])
   Counts codepoints in s from position i to j (both inclusive).
   Returns [false, position] if an invalid byte sequence is found.
   lax=true enables nonstrict decoding (surrogates, > 0x10FFFF).
   Default: i=1, j=#s (end of string)."
  [^String s & [i j lax]]
  (let [slen (long (.length s))
        i-raw (long (or i 1))
        j-raw (if (nil? j) -1 (long j))
        i (long (if (neg? i-raw) (+ slen i-raw 1) i-raw))
        j (long (if (= j-raw -1) slen (if (neg? j-raw) (+ slen j-raw 1) j-raw)))
        decode (if lax decode-utf8-lax decode-utf8)]
    (when (or (< i 1) (> i (unchecked-inc slen)))
      (throw (ex-info "out of bounds" {:type :error})))
    (when (> j slen)
      (throw (ex-info "out of bounds" {:type :error})))
    (loop [pos i cnt (long 0)]
      (cond
        (> pos j) cnt
        (> pos slen) cnt
        :else
        (let [decoded (decode s pos)]
          (if (nil? decoded)
            [false pos]
            (let [[_ seqlen] decoded]
              (recur (unchecked-add pos (long seqlen)) (unchecked-inc cnt)))))))))

(defn- char-end
  "Return the 1-based last byte position of the UTF-8 character starting at p in s.
   Scans forward from p+1 consuming continuation bytes (0x80-0xBF). Works for
   both strict and lax (extended) UTF-8 sequences. When p > slen (past-end
   sentinel), returns p unchanged."
  [^String s ^long p]
  (let [slen (long (.length s))]
    (if (> p slen)
      p
      (loop [q (unchecked-inc p)]
        (if (and (<= q slen) (continuation? (int (.charAt s (unchecked-dec q)))))
          (recur (unchecked-inc q))
          (unchecked-dec q))))))

(defn lua-offset
  "utf8.offset(s, n [, i])
   Returns two values: the byte position of the n-th codepoint and its last byte.
   - n=0: position of the codepoint containing i (backs over continuation bytes)
   - n>0: advance n-1 codepoints from i (n=1 returns i itself)
   - n<0: go back |n| codepoints from i
   Default i: 1 for n>=0, #s+1 for n<0.
   Returns nil if the requested position is out of the string.
   Throws 'position out of bounds' if explicit i is outside [1, #s+1].
   Throws 'continuation byte' if i points to a continuation byte (n≠0)."
  [^String s n & [i-arg]]
  (let [slen (long (.length s))
        n (long n)
        i-explicit? (some? i-arg)
        i-raw (long (or i-arg (if (>= n 0) 1 (unchecked-inc slen))))
        i (long (if (and i-explicit? (neg? i-raw)) (+ slen i-raw 1) i-raw))]
    (when i-explicit?
      (when (or (< i 1) (> i (unchecked-inc slen)))
        (throw (ex-info "position out of bounds" {:type :error}))))
    (when (and (not (zero? n)) (<= i slen) (continuation? (int (.charAt s (unchecked-dec i)))))
      (throw (ex-info "continuation byte" {:type :error})))
    (cond
      (zero? n)
      ;; Back up over continuation bytes to find the lead byte
      (let [p (loop [p i]
                (if (and (> p 1) (<= p slen) (continuation? (int (.charAt s (unchecked-dec p)))))
                  (recur (unchecked-dec p))
                  p))]
        [p (char-end s p)])

      (pos? n)
      (loop [p i remaining (unchecked-dec n)]
        (if (zero? remaining)
          (when (<= p (unchecked-inc slen))
            [p (char-end s p)])
          (if (> p slen)
            nil
            ;; Advance past the current sequence: skip lead + all following continuation bytes
            (let [p1 (loop [q (unchecked-inc p)]
                       (if (and (<= q slen) (continuation? (int (.charAt s (unchecked-dec q)))))
                         (recur (unchecked-inc q))
                         q))]
              (recur (long p1) (unchecked-dec remaining))))))

      :else
      (loop [p i remaining (- n)]
        (if (zero? remaining)
          [p (char-end s p)]
          (if (< p 2)
            nil
            (let [prev-p (long (loop [q (unchecked-dec p)]
                                 (if (and (> q 0) (continuation? (int (.charAt s (unchecked-dec q)))))
                                   (recur (unchecked-dec q))
                                   q)))]
              (if (< prev-p 1)
                (throw (ex-info "continuation byte" {:type :error}))
                (recur prev-p (unchecked-dec remaining))))))))))

;; =============================================================================
;; Export as Lua library table
;; =============================================================================

;; The charpattern matches exactly one UTF-8 sequence (official Lua 5.3 value).
;; Bytes as Java chars: \u0000=null, \u007F=DEL, \u00C2-\u00FD=valid leads, \u0080-\u00BF=continuations.
(def charpattern "[\u0000-\u007F\u00C2-\u00FD][\u0080-\u00BF]*")

(def utf8-lib
  "The complete utf8 library for Lua."
  {"char" lua-char
   "codes" lua-codes
   "codepoint" lua-codepoint
   "len" lua-len
   "offset" lua-offset
   "charpattern" charpattern})
