module  {:extern "ConsoleIO"} ConsoleIO
{
  method {:extern "INTERNAL__WriteLine"} WriteLine(line: string)
  method {:extern "INTERNAL__ReadLine"} ReadLine() returns (line: string)
}
