(module
  (func (export "f") (result i64)
    (local i32) (local i64)     ;; local 0 : i32, local 1 : i64
    i32.const 1
    local.set 0
    local.get 0
    drop                        ;; local 0 dead from here
    i64.const 7
    local.set 1                 ;; disjoint range -> linear scan gives it slot 0
    local.get 1))
