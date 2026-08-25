(module
  (func (export "f") (result i32)
    (local i32) (local i32)
    i32.const 1
    local.set 0        ;; local 0: def then use, dead afterwards
    local.get 0
    drop
    i32.const 7
    local.set 1        ;; local 1: disjoint live range -> coalescable into slot 0
    local.get 1))
