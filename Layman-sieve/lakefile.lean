import Lake
open Lake DSL

package laymansieve

@[default_target]
lean_lib LaymanSieve where
  roots := #[`Proof, `Residues]
