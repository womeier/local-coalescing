(module
  (func (export "f") (param i32) (result i32)
    (local i32 i32)
    i32.const 42
    local.set 1          ;; local 1: last touched inside the loop body
    loop
      local.get 1
      drop
      i32.const 7
      local.set 2        ;; local 2: first defined here, dead outside the loop
      local.get 2
      drop
    end
    local.get 0))
