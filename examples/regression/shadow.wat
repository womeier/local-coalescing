(module
  (func (export "f") (param i32) (result i32)
    (local i32 i32)
    i32.const 1
    local.set 1        ;; local 1 written once, never read
    block
      block
        i32.const 2
        local.set 2    ;; local 2 first defined here, two levels down
      end
      i32.const 3
      local.set 2      ;; ... and again at the top level of the outer body
    end
    local.get 2))
