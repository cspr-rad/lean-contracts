import Lake
open Lake DSL

package «contracts» where
  -- add package configuration options here

lean_lib «Contracts» where
  -- add library configuration options here

@[default_target]
lean_exe «contracts» where
  root := `Main
