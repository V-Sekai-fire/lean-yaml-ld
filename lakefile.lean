import Lake
open Lake DSL

package «lean-yaml-ld»

@[default_target]
lean_lib YamlLd

lean_lib JsonLd where
  roots := #[`JsonLd, `JsonLd.Iri, `JsonLd.Remote]
/-- Finds `<script>` elements in HTML for the test runner. The library does not read HTML. -/
lean_lib HtmlScripts

lean_exe yamlld_witness where
  root := `YamlLdWitness
lean_exe jsonld_suite where
  root := `JsonLdSuite
