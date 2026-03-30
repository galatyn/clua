(ns clua.stdlib.xoshiro256
  "xoshiro256** PRNG — matches Lua 5.5's math.random algorithm exactly.

   State: long-array of 4 elements (256-bit state).
   Algorithm: xoshiro256** (Blackman & Vigna, 2019).
   Reference: https://prng.di.unimi.it/xoshiro256starstar.c

   Seeding uses the same scheme as Lua 5.5 (lmathlib.c):
     s[0] = n1, s[1] = 0xff, s[2] = n2, s[3] = 0
   followed by 16 warm-up calls to discard the initial values.")

(set! *warn-on-reflection* true)
(set! *unchecked-math* :warn-on-boxed)

;; ============================================================================
;; Core algorithm
;; ============================================================================

(defn next-long
  "Advance state and return the next pseudo-random 64-bit value.
   State must be a long-array of length 4.
   Implements xoshiro256** with sequential (in-place) state updates,
   matching the reference implementation at https://prng.di.unimi.it/xoshiro256starstar.c"
  ^long [^longs state]
  (let [s1 (aget state 1)
        result (unchecked-multiply (Long/rotateLeft (unchecked-multiply s1 5) 7) 9)
        t (bit-shift-left s1 17)]
    (aset state 2 (bit-xor (aget state 2) (aget state 0)))
    (aset state 3 (bit-xor (aget state 3) s1))
    (aset state 1 (bit-xor s1 (aget state 2)))              ; uses new state[2]
    (aset state 0 (bit-xor (aget state 0) (aget state 3)))  ; uses new state[3]
    (aset state 2 (bit-xor (aget state 2) t))
    (aset state 3 (Long/rotateLeft (aget state 3) 45))
    result))

;; ============================================================================
;; Seeding
;; ============================================================================

(defn seed!
  "Seed state from two 64-bit integers n1 and n2, matching Lua 5.5 semantics.
   Equivalent to lmathlib.c setseed(state, n1, n2)."
  [^longs state ^long n1 ^long n2]
  (aset state 0 n1)
  (aset state 1 (long 0xff))
  (aset state 2 n2)
  (aset state 3 (long 0))
  ;; Warm up: discard 16 values to spread the seed
  (dotimes [_ 16]
    (next-long state)))

(defn make-state
  "Create and seed a fresh xoshiro256** state array."
  ^longs [^long n1 ^long n2]
  (let [state (long-array 4)]
    (seed! state n1 n2)
    state))

;; ============================================================================
;; Random value generation
;; ============================================================================

(defn next-double
  "Return a float in [0, 1) — (nextrand >>> 11) * (1 / 2^53).
   Matches Lua 5.5 math.random() with no arguments."
  ^double [^longs state]
  (* (double (unsigned-bit-shift-right (next-long state) 11))
     (double (/ 1.0 9007199254740992.0))))                  ; 1 / 2^53

(defn next-long-in
  "Return a random long in [0, limit] inclusive where limit >= 0.
   Uses rejection sampling to avoid modulo bias: generates values in [0, 2^k)
   where 2^k is the smallest power of 2 > limit, rejects out-of-range values."
  ^long [^longs state ^long limit]
  (if (zero? limit)
    0
    ;; Build a bitmask that covers all bits of limit (smear highest bit downward)
    (let [m1 (bit-or limit (unsigned-bit-shift-right limit 1))
          m2 (bit-or m1 (unsigned-bit-shift-right m1 2))
          m3 (bit-or m2 (unsigned-bit-shift-right m2 4))
          m4 (bit-or m3 (unsigned-bit-shift-right m3 8))
          m5 (bit-or m4 (unsigned-bit-shift-right m4 16))
          mask (bit-or m5 (unsigned-bit-shift-right m5 32))]
      (loop []
        (let [r (bit-and ^long (next-long state) mask)]
          (if (<= r limit)
            r
            (recur)))))))
