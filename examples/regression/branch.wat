(module
  (func (export "f") (param i32) (result i32)
    (local i32) (local i32)     ;; locals 1, 2 (param is local 0)
    i32.const 42
    local.set 1                 ;; def local1
    local.get 1
    drop                        ;; local1 dead from here
    local.get 0
    (if (then
      i32.const 99
      local.set 2))             ;; def local2 -- only on the taken path
    local.get 2))               ;; read local2 even when the branch was skipped
