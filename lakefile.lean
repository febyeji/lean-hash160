import Lake

open Lake DSL

package lean_hash160 where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib LeanHash160

@[test_driver]
lean_exe tests where
  root := `Tests.Main
