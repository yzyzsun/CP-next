{ name = "zord"
, dependencies =
  [ "ansi"
  , "console"
  , "debug"
  , "node-fs"
  , "node-fs-aff"
  , "node-readline"
  , "now"
  , "ordered-collections"
  , "parsing"
  , "psci-support"
  , "spec"
  , "transformers"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
