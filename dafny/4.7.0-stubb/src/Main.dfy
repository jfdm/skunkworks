include "ConsoleIO.dfy"

module Main
{

  import opened ConsoleIO


  method {:main} Main()
    decreases *
  {
    print "a\n";
    WriteLine("sss");
    var s := ReadLine();
    WriteLine(s);
  }


}
