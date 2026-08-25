(module
  (func (export "f") (result i32)
    (local i32) (local i32)
    i32.const 1
    local.set 0        ;; first write to local 0
    i32.const 2
    local.set 0        ;; SECOND write -> not SSA
    i32.const 7
    local.set 1
    local.get 1))
