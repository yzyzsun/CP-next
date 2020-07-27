{ name = "zord"
, dependencies =
  [ "ansi"
  , "console"
  , "debug"
  , "node-fs"
  , "node-readline"
  , "ordered-collections"
  , "parsing"
  , "psci-support"
  , "transformers"
  ]
, packages = ./packages.dhall
, sources = [ "src/**/*.purs" ]
}
