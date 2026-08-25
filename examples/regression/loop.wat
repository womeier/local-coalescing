(module
  (func (export "f") (result i32)
    (local i32) (local i32)
    (loop $L
      i32.const 1
      local.set 0        ;; def local0, one syntactic write
      local.get 0
      drop
      i32.const 7
      local.set 1        ;; def local1, disjoint source-order range
      local.get 1
      drop)
    local.get 1))
