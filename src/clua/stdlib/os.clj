(ns clua.stdlib.os
  "Lua 5.3 os library - safe sandboxed subset.

   Implements the read-only / computation-only functions:
     clock, date, difftime, setlocale, time

   VFS-aware factory (make-os-table) adds:
     tmpname, remove, rename, getenv, execute, exit"
  (:require [clojure.string :as str]
            [clua.interpreter.env :as env]
            [clua.interpreter.tables :as tables]
            [clua.stdlib.io :as lua-io])
  (:import (java.lang.management ManagementFactory)
           (java.time Instant LocalDateTime ZoneId ZoneOffset ZonedDateTime)
           (java.time.format DateTimeFormatter TextStyle)
           (java.time.temporal IsoFields)
           (java.util Locale)))
(set! *warn-on-reflection* true)


;; =============================================================================
;; os.clock
;; =============================================================================

(defn lua-clock
  "os.clock() - Returns an approximation of CPU time used by the program, in seconds."
  []
  (let [bean (ManagementFactory/getThreadMXBean)]
    (if (.isCurrentThreadCpuTimeSupported bean)
      (/ (double (.getCurrentThreadCpuTime bean)) 1.0e9)
      0.0)))

;; =============================================================================
;; os.difftime
;; =============================================================================

(defn lua-difftime
  "os.difftime(t2, t1) - Returns the difference in seconds from t1 to t2."
  [t2 t1]
  (- (long t2) (long t1)))

;; =============================================================================
;; os.time
;; =============================================================================

(defn- table-long
  "Get a numeric field from a Lua table as a long, returning default if absent.
   Throws a Lua error if the field exists but is not an integer value."
  [t k default]
  (let [v (tables/table-get t k)]
    (cond
      (nil? v) default
      (integer? v) (long v)
      (float? v) (let [d (double v)]
                   (if (== d (Math/floor d))
                     (long d)
                     (throw (ex-info (str "field '" k "' is not an integer")
                                     {:type :error}))))
      :else (throw (ex-info (str "field '" k "' is not an integer")
                            {:type :error})))))

(defn lua-time
  "os.time([table]) - Returns current Unix timestamp, or converts a date table to a timestamp.
   When a table is given, normalizes out-of-range fields and writes them back (Lua 5.3.3+)."
  ([] (quot (System/currentTimeMillis) 1000))
  ([t]
   (if (nil? t)
     (quot (System/currentTimeMillis) 1000)
     (let [year (table-long t "year" nil)
           month (table-long t "month" nil)
           day (table-long t "day" nil)]
       (when (nil? year) (throw (ex-info "field 'year' missing in date table" {:type :error})))
       (when (nil? month) (throw (ex-info "field 'month' missing in date table" {:type :error})))
       (when (nil? day) (throw (ex-info "field 'day' missing in date table" {:type :error})))
       (when (or (< (long year) -999999999) (> (long year) 999999999))
         (throw (ex-info "field 'year' is out-of-bound" {:type :error})))
       (let [hour (table-long t "hour" 12)
             min (table-long t "min" 0)
             sec (table-long t "sec" 0)
             ;; Build at midnight then add time to normalize overflow/underflow
             base (LocalDateTime/of (int year) (int month) (int day) 0 0 0)
             ldt (-> base (.plusHours hour) (.plusMinutes min) (.plusSeconds sec))
             zdt (.atZone ldt (ZoneId/systemDefault))
             epoch (.toEpochSecond zdt)]
         ;; Write back normalized fields (Lua 5.3.3+)
         (tables/table-set! t "year" (long (.getYear ldt)))
         (tables/table-set! t "month" (long (.getMonthValue ldt)))
         (tables/table-set! t "day" (long (.getDayOfMonth ldt)))
         (tables/table-set! t "hour" (long (.getHour ldt)))
         (tables/table-set! t "min" (long (.getMinute ldt)))
         (tables/table-set! t "sec" (long (.getSecond ldt)))
         (tables/table-set! t "wday" (long (-> ldt .getDayOfWeek .getValue (mod 7) long inc)))
         (tables/table-set! t "yday" (long (.getDayOfYear ldt)))
         (tables/table-set! t "isdst" false)
         epoch)))))

;; =============================================================================
;; os.date
;; =============================================================================

(def ^:private fmt-zone-offset (DateTimeFormatter/ofPattern "Z"))
(def ^:private fmt-zone-name (DateTimeFormatter/ofPattern "z"))

(defn- week-num
  "Week-of-year (00-53) counting from the given first day of week (0=Sun, 1=Mon...)."
  [^ZonedDateTime zdt ^long first-dow-value]
  (let [d (long (.getDayOfYear zdt))
        ;; weekday of Jan 1, in Sunday-based numbering (0=Sun, 6=Sat)
        jan1 (ZonedDateTime/of (.getYear zdt) 1 1 0 0 0 0 (.getZone zdt))
        j1-sun (long (mod (.getValue (.getDayOfWeek jan1)) 7))
        ;; shift to the requested first-day-of-week numbering
        j1-adj (long (mod (unchecked-add j1-sun (unchecked-subtract 7 first-dow-value)) 7))
        adj (if (zero? j1-adj) 7 j1-adj)]
    (quot (unchecked-add (unchecked-add d (long adj)) -1) 7)))

(defn- format-spec
  "Format a single strftime specifier character against the given ZonedDateTime."
  [spec ^ZonedDateTime zdt]
  (let [dow-val (.getValue (.getDayOfWeek zdt))             ;; 1=Mon...7=Sun (Java)
        dow-sun (mod dow-val 7)                             ;; 0=Sun...6=Sat
        hour (.getHour zdt)
        h12 (let [h (long (mod hour 12))] (if (zero? h) 12 h))
        yr (.getYear zdt)
        mo (.getMonthValue zdt)
        day (.getDayOfMonth zdt)
        mn (.getMinute zdt)
        sec (.getSecond zdt)]
    (case spec
      \% "%"
      \n "\n"
      \t "\t"
      ;; Year
      \Y (format "%04d" yr)
      \y (format "%02d" (mod yr 100))
      \C (format "%02d" (quot yr 100))
      ;; Month / day
      \m (format "%02d" mo)
      \d (format "%02d" day)
      \e (format "%2d" day)
      ;; Hours / minutes / seconds
      \H (format "%02d" hour)
      \I (format "%02d" h12)
      \k (format "%2d" hour)
      \l (format "%2d" h12)
      \M (format "%02d" mn)
      \S (format "%02d" sec)
      ;; Day of year / week
      \j (format "%03d" (.getDayOfYear zdt))
      \w (str dow-sun)
      \u (str dow-val)
      \U (format "%02d" (week-num zdt 0))                   ;; Sunday-first
      \W (format "%02d" (week-num zdt 1))                   ;; Monday-first
      \V (format "%02d" (.get zdt IsoFields/WEEK_OF_WEEK_BASED_YEAR))
      ;; Named day / month (English, C-locale style)
      \A (.getDisplayName (.getDayOfWeek zdt) TextStyle/FULL Locale/ENGLISH)
      \a (.getDisplayName (.getDayOfWeek zdt) TextStyle/SHORT Locale/ENGLISH)
      \B (.getDisplayName (.getMonth zdt) TextStyle/FULL Locale/ENGLISH)
      \b (.getDisplayName (.getMonth zdt) TextStyle/SHORT Locale/ENGLISH)
      \h (.getDisplayName (.getMonth zdt) TextStyle/SHORT Locale/ENGLISH)
      ;; AM/PM
      \p (if (< hour 12) "AM" "PM")
      \P (if (< hour 12) "am" "pm")
      ;; Timezone
      \z (.format zdt fmt-zone-offset)
      \Z (.format zdt fmt-zone-name)
      ;; Composites — expanded directly to avoid circular dependency
      \T (format "%02d:%02d:%02d" hour mn sec)
      \R (format "%02d:%02d" hour mn)
      \D (format "%02d/%02d/%02d" mo day (mod yr 100))
      \F (format "%04d-%02d-%02d" yr mo day)
      \r (format "%02d:%02d:%02d %s" h12 mn sec (if (< hour 12) "AM" "PM"))
      \X (format "%02d:%02d:%02d" hour mn sec)
      \x (format "%02d/%02d/%02d" mo day (mod yr 100))
      \c (format "%s %s %2d %02d:%02d:%02d %04d"
           (.getDisplayName (.getDayOfWeek zdt) TextStyle/SHORT Locale/ENGLISH)
           (.getDisplayName (.getMonth zdt) TextStyle/SHORT Locale/ENGLISH)
           day hour mn sec yr)
      ;; Unknown specifier — error
      (throw (ex-info (str "invalid conversion specifier '%" spec "'")
                      {:type :error})))))

(defn- format-date-str
  "Apply a strftime-like format string to the given ZonedDateTime."
  [^String fmt ^ZonedDateTime zdt]
  (let [sb (StringBuilder.)
        n (count fmt)]
    (loop [i 0]
      (cond
        (>= i n)
        (.toString sb)
        (= (.charAt fmt i) \%)
        (if (< (inc i) n)
          (do (.append sb (format-spec (.charAt fmt (inc i)) zdt))
              (recur (+ i 2)))
          (throw (ex-info "invalid conversion specifier '%'"
                          {:type :error})))
        :else
        (do (.append sb (.charAt fmt i))
            (recur (inc i)))))))

(defn- make-date-table
  "Build a Lua table from a ZonedDateTime (the '*t' format)."
  [^ZonedDateTime zdt]
  (let [t (tables/make-table)
        wday (-> zdt .getDayOfWeek .getValue (mod 7) long inc)] ;; 1=Sun...7=Sat
    (tables/table-set! t "year" (.getYear zdt))
    (tables/table-set! t "month" (.getMonthValue zdt))
    (tables/table-set! t "day" (.getDayOfMonth zdt))
    (tables/table-set! t "hour" (.getHour zdt))
    (tables/table-set! t "min" (.getMinute zdt))
    (tables/table-set! t "sec" (.getSecond zdt))
    (tables/table-set! t "wday" wday)
    (tables/table-set! t "yday" (.getDayOfYear zdt))
    (tables/table-set! t "isdst" false)
    t))

(defn lua-date
  "os.date([format [, time]]) - Returns date/time as a formatted string or table.
   If format starts with '!', uses UTC. The special format '*t' returns a table."
  ([] (lua-date "%c" nil))
  ([fmt] (lua-date fmt nil))
  ([fmt time-val]
   (let [fmt (or fmt "%c")
         utc? (str/starts-with? fmt "!")
         fmt-str (if utc? (subs fmt 1) fmt)
         zdt (if time-val
               (ZonedDateTime/ofInstant
                 (Instant/ofEpochSecond (long time-val))
                 (if utc? ZoneOffset/UTC (ZoneId/systemDefault)))
               (if utc?
                 (ZonedDateTime/now ZoneOffset/UTC)
                 (ZonedDateTime/now (ZoneId/systemDefault))))]
     (if (= fmt-str "*t")
       (make-date-table zdt)
       (format-date-str fmt-str zdt)))))

;; =============================================================================
;; os.setlocale
;; =============================================================================

(def ^:private valid-categories
  #{"all" "collate" "ctype" "monetary" "numeric" "time"})

(defn- posix-locale->java
  "Parse a POSIX locale name (e.g. 'pt_BR', 'pt_BR.UTF-8', 'C', 'POSIX') to a
   java.util.Locale, or nil if the locale string cannot be resolved to a valid locale."
  [^String locale-str]
  (cond
    (or (= locale-str "C") (= locale-str "POSIX"))
    Locale/ROOT

    (= locale-str "")
    (Locale/getDefault)

    :else
    (let [base (-> locale-str
                   (str/replace #"\..*" "")                 ; strip .UTF-8 encoding suffix
                   (str/replace #"@.*" ""))                 ; strip @modifier
          bcp47 (str/replace base "_" "-")                  ; pt_BR -> pt-BR
          loc (Locale/forLanguageTag bcp47)
          lang (.getLanguage loc)]
      ;; Require non-empty language AND valid POSIX format: 2-3 lowercase letters,
      ;; optionally followed by underscore + 2-3 uppercase territory letters.
      ;; This filters out syntactically-valid-but-nonsensical BCP47 tags like "invalid".
      (when (and (seq lang)
                 (re-matches #"[a-z]{2,3}(-[A-Z]{2,3})?" bcp47))
        loc))))

(defn lua-setlocale
  "os.setlocale([locale [, category]]) - Set or query the current locale.
   Affects number formatting (string.format, io.write, tostring) and parsing (tonumber)
   when category is 'numeric' or 'all'. Other categories are accepted but are no-ops
   in the sandbox. Returns the locale name on success, nil on failure."
  ([] (lua-setlocale nil nil))
  ([locale] (lua-setlocale locale nil))
  ([locale category]
   (when (and category (not (contains? valid-categories category)))
     (throw (ex-info "bad argument #2 to 'setlocale' (invalid category)"
                     {:type :error})))
   (let [cat (or category "all")]
     (if (nil? locale)
       ;; Query: return current locale name without changing it
       (env/get-numeric-locale-name env/*current-env*)
       ;; Set: parse the POSIX locale name
       (when-let [java-loc (posix-locale->java locale)]
         (when (or (= cat "numeric") (= cat "all"))
           (env/set-numeric-locale! env/*current-env* java-loc locale))
         ;; "collate" and "ctype" are not supported in CLua (no JVM locale collation
         ;; or character-class overrides); return nil so callers know they failed.
         (when-not (or (= cat "collate") (= cat "ctype"))
           ;; Return the canonical form: "C" for ROOT, original string otherwise
           (if (= java-loc Locale/ROOT) "C" locale)))))))

;; =============================================================================
;; Library map
;; =============================================================================

(def os-lib
  {"clock" lua-clock
   "date" lua-date
   "difftime" lua-difftime
   "setlocale" lua-setlocale
   "time" lua-time})

;; =============================================================================
;; VFS-aware os table factory
;; =============================================================================

(def ^:private tmp-counter (atom 0))

(defn make-os-table
  "Create an os library map with VFS-aware functions.
   tmpname pre-creates a MemoryFile in vfs; remove/rename operate on vfs.
   env-vars is a map of string→string exposed via os.getenv (default {})."
  ([vfs] (make-os-table vfs {}))
  ([vfs env-vars]
   (merge os-lib
          {"tmpname" (fn []
                       (let [n (str "/tmp/lua_" (swap! tmp-counter inc))]
                         (swap! vfs assoc n (lua-io/make-memory-file))
                         n))
           "remove" (fn [path]
                      (let [p (str path)]
                        (if (contains? @vfs p)
                          (do (swap! vfs dissoc p) true)
                          [nil (str p ": No such file or directory") 2])))
           "rename" (fn [old new-path]
                      (let [o (str old)
                            n (str new-path)]
                        (if-let [mf (get @vfs o)]
                          (do (swap! vfs #(-> % (dissoc o) (assoc n mf)))
                              true)
                          [nil (str o ": No such file or directory") 2])))
           "getenv" (fn [name] (get env-vars (str name)))
           "execute" (fn [& _] nil)
           "exit" (fn
                    ([] (throw (ex-info "exit" {:type :exit :code 0})))
                    ([code]
                     (let [n (cond
                               (= code true)  0
                               (= code false) 1
                               (number? code) (long (double code))
                               :else          0)]
                       (throw (ex-info "exit" {:type :exit :code n})))))})))
