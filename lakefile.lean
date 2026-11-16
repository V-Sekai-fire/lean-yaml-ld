import Lake
open Lake DSL

package «lean-yaml-ld»

@[default_target]
lean_lib YamlLd

lean_exe yamlld_witness where
  root := `YamlLdWitness
lean_exe yamlld_conform where
  root := `YamlLdConform
