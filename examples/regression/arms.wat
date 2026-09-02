(module
  (func (export "f") (param i32) (result i32)
    (local i32 i32)
    i32.const 42
    local.set 1        ;; local 1 dies right after
    local.get 1
    drop
    local.get 0
    if (result i32)
      i32.const 7
      local.set 2      ;; local 2 first defined here, in arm 1
      i32.const 0
    else
      local.get 2      ;; ... and read only in arm 2
    end))
