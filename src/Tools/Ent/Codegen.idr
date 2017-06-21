module Tools.Ent.Codegen

outputs : String -> String
outputs s = """
.assembly extern mscorlib {}
.assembly hello {}
.method static public void main() cil managed
{ .entrypoint
""" ++ "  ldstr \"" ++ s ++ "\"" ++ """
  call void [mscorlib]System.Console::WriteLine(class System.String)
  ret
}
"""

main : IO ()
main = do putStrLn $ outputs "Hello world"
          pure ()
