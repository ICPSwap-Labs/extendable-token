let upstream = https://github.com/dfinity/vessel-package-set/releases/download/mo-0.6.21-20220215/package-set.dhall
let Package =
    { name : Text, version : Text, repo : Text, dependencies : List Text }

let
  -- This is where you can add your own packages to the package-set
  additions =
    [
      { name = "base"
      , repo = "https://github.com/dfinity/motoko-base"
      , version = "moc-0.6.24"
      , dependencies = [] : List Text
      },
      { dependencies = [ "base" ]
      , name = "ic-commons"
      , repo = "https://github.com/ICPSwap-Labs/ic-commons"
      , version = "0.0.2"
      },
      { name = "cap"
      , repo = "https://github.com/Psychedelic/cap-motoko-library"
      , version = "v1.0.4"
      , dependencies = ["base"] : List Text
      },
    ]
let
  {- This is where you can override existing packages in the package-set

     For example, if you wanted to use version `v2.0.0` of the foo library:
     let overrides = [
         { name = "foo"
         , version = "v2.0.0"
         , repo = "https://github.com/bar/foo"
         , dependencies = [] : List Text
         }
     ]
  -}
  overrides =
    [] : List Package

in  upstream # additions # overrides
