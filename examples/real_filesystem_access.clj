;; examples/real_filesystem_access.clj
;;
;; Demonstrates mounting real files and directories into the CLua VFS
;; so Lua scripts can access them via the standard io.* API.
;;
;; API (clua.stdlib.vfs namespace):
;;   (vfs/mount-file!  sandbox real-path vfs-path)         ; single file
;;   (vfs/mount-file!  sandbox real-path vfs-path opts)    ; with {:read-only? false}
;;   (vfs/mount-dir!   sandbox real-dir  vfs-prefix)       ; whole directory (recursive)
;;   (vfs/flush-vfs!   sandbox vfs-prefix real-dir)        ; write MemoryFile outputs to disk
;;   (vfs/with-sandbox [sb ...] ...)                       ; auto-close file handles

(require '[clua.core :as clua]
         '[clua.stdlib.core :as stdlib]
         '[clua.stdlib.vfs :as vfs])

;; ---------------------------------------------------------------------------
;; Example 1 — Read a real file (read-only, default)
;; ---------------------------------------------------------------------------
;;
;; Assume /tmp/hello.txt contains "Hello from the real filesystem!\n"

(spit "/tmp/hello.txt" "Hello from the real filesystem!\n")

(vfs/with-sandbox [sb (vfs/mount (stdlib/sandbox-full)
                                 [{:type :file :real "/tmp/hello.txt" :vfs "hello.txt"}])]
  (let [result (clua/execute sb "
    local f = assert(io.open('hello.txt', 'r'))
    local content = f:read('a')
    f:close()
    return content
  ")]
    (println "Read content:" (:result result))
    ;; => "Hello from the real filesystem!\n"

    ;; Writing to a read-only mount is denied at io.open time
    (let [deny (clua/execute sb "
      local f, err = io.open('hello.txt', 'w')
      return f == nil, err
    ")]
      (println "Write denied:" (:result deny)))))
    ;; => [true "hello.txt: Permission denied"]

;; ---------------------------------------------------------------------------
;; Example 2 — Write-through to a real file
;; ---------------------------------------------------------------------------
;;
;; With {:read-only? false} writes go directly to the real file via
;; RandomAccessFile — no flush step needed.

(spit "/tmp/output.txt" "")          ; ensure the file exists

(vfs/with-sandbox [sb (vfs/mount (stdlib/sandbox-full)
                                 [{:type :file :real "/tmp/output.txt" :vfs "output.txt"
                                   :read-only? false}])]
  (clua/execute sb "
    local f = assert(io.open('output.txt', 'w'))
    for i = 1, 3 do
      f:write('line ' .. i .. '\\n')
    end
    f:close()
  ")
  (println "Written to real file:")
  (println (slurp "/tmp/output.txt")))
;; => line 1
;;    line 2
;;    line 3

;; ---------------------------------------------------------------------------
;; Example 3 — Mount a directory (read-only)
;; ---------------------------------------------------------------------------
;;
;; Files in /tmp/data/ become accessible under the "data/" VFS prefix.

(.mkdirs (java.io.File. "/tmp/data/subdir"))
(spit "/tmp/data/config.txt"        "color=blue\nsize=42\n")
(spit "/tmp/data/subdir/values.csv" "a,b,c\n1,2,3\n")

(vfs/with-sandbox [sb (vfs/mount (stdlib/sandbox-full)
                                 [{:type :dir :real "/tmp/data" :vfs "data/"}])]
  (let [result (clua/execute sb "
    local cfg = {}
    for line in io.lines('data/config.txt') do
      local k, v = line:match('^(%w+)=(.+)$')
      if k then cfg[k] = v end
    end

    local first_line
    local f = assert(io.open('data/subdir/values.csv', 'r'))
    first_line = f:read('l')
    f:close()

    return cfg.color, tonumber(cfg.size), first_line
  ")]
    (println "Config:" (:result result))))
    ;; => ["blue" 42 "a,b,c"]

;; ---------------------------------------------------------------------------
;; Example 4 — Script writes to in-memory VFS, then flush to disk
;; ---------------------------------------------------------------------------
;;
;; Input files are real (read-only mounts). Script writes to in-memory VFS
;; paths. After execution, flush the written paths back to disk.

(.mkdirs (java.io.File. "/tmp/inputs"))
(.mkdirs (java.io.File. "/tmp/outputs"))
(spit "/tmp/inputs/numbers.txt" "3\n1\n4\n1\n5\n9\n2\n6\n")

(vfs/with-sandbox [sb (vfs/mount (stdlib/sandbox-full)
                                 [{:type :file :real "/tmp/inputs/numbers.txt"
                                   :vfs "inputs/numbers.txt"}])]
  (clua/execute sb "
    local nums = {}
    for line in io.lines('inputs/numbers.txt') do
      nums[#nums + 1] = tonumber(line)
    end
    table.sort(nums)
    local f = assert(io.open('outputs/sorted.txt', 'w'))
    for _, n in ipairs(nums) do
      f:write(n .. '\\n')
    end
    f:close()
  ")

  ;; Flush all VFS entries under "outputs/" to /tmp/outputs/
  (let [flushed (vfs/flush-vfs! sb "outputs/" "/tmp/outputs")]
    (println "Flushed:" flushed)
    ;; => ["outputs/sorted.txt"]
    (println "Sorted output:")
    (println (slurp "/tmp/outputs/sorted.txt"))))
  ;; => 1
  ;;    1
  ;;    2
  ;;    3
  ;;    4
  ;;    5
  ;;    6
  ;;    9
