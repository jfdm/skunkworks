namespace ConsoleIO {


using System;
using System.IO;
using Dafny;


  public partial class __default {
    public static void INTERNAL__WriteLine(ISequence<Rune> line) {
      Console.WriteLine(line.ToVerbatimString(false));
    }

    public static ISequence<Rune> INTERNAL__ReadLine() {
      var line = Console.ReadLine();
      return Sequence<Rune>.UnicodeFromString(line);
    }
  }}
