import Lake
open Lake DSL

package «CambridgeSemantics» where
  -- add any package configuration options here

@[default_target]
lean_lib «CambridgeSemantics» where
  -- add any library configuration options here

meta if get_config? env = some "dev" then -- dev is so not everyone has to build it
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"
