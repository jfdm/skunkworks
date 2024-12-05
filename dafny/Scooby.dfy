method printLn(s : string)
{
  print s, "\n";
}

method Main()
{
  var s := "Hello world";
  print s, "\n";
  printLn(s);
}
