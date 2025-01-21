# Project Stubb for Dafny 4.7.0 and Dotnet 6.

Our lab machines have older versions of Dafny and Dotnet.
This stubb is designed to work with the older versions and do golden file testing.

The experience in Dafny 4.7.0 is not ideal,
hence the fancy layering of makefiles.
Our machines also do not have `lit` installed,
so we use Idris2 as the test harnerss.

All of this is temporary as Dafny 4.8.x and Dotnet 8 make the situation better.
Especially with `toml` configuration files.

If you know how to get dotnet 6 and dafny 4.7.0 to spit out a single binary executable them please let me know.
