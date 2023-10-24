module TestVirtualMachine

open Syntax
open NUnit.Framework
open TargetCode
open Utils
open AddressResolution
open GenCode
open VirtualMachine
open GenComputation
open Environment

[<TestFixture>]
type Fixture () =

    [<SetUp>]
    member this.setup () =
        ()

    [<Test>]
    member this.sumTwoInts() =
        let e = parseExpr "3 + 2"
        let _, ty, code = 
            match run (genExprR Context.empty e) with
            | Result(code, _) ->
                code
            | Error(_, _) ->
                failwith "code generation failed"

        match ty with
        | Int(_) ->
            ()
        | _ ->
            failwith "expected type of '3 + 2' to be int"

        let code' = List.concat [code ; [Halt]]
        let code'' = resolve code'
        let result = execute code''

        Assert.That( (result = 5) )

    [<Test>]
    member this.moreMath() =
        let e = parseExpr "(3 + 2 - 1) * 6"
        let _, ty, code = 
            match run (genExprR Context.empty e) with
            | Result(code, _) ->
                code
            | Error(_, _) ->
                failwith "code generation failed"

        match ty with
        | Int(_) ->
            ()
        | _ ->
            failwith "expected type of '(3 + 2 - 1) * 6' to be int"

        let code' = List.concat [code ; [Halt]]
        let code'' = resolve code'
        let result = execute code''

        Assert.That( (result = 24) )

    [<Test>]
    member this.returnOne() =
        let e = parseProg """
            int a;

            fun int main() {
              return 1;
            }
        """
        let code = 
            match run (genProg e) with
            | Result(code, _) ->
                code
            | Error(_, _) ->
                failwith "code generation failed"

        let code' = resolve code
        let result = execute code'

        Assert.That( (result = 1) )        


    [<Test>]
    member this.assignReturn() =
        let e = parseProg """
            int a;

            fun int main() {
              a <- 2;
              return a;
            }
        """
        let code = 
            match run (genProg e) with
            | Result(code, _) ->
                code
            | Error(msg, _) ->
                failwith <| "code generation failed with error: " + msg

        let code' = resolve code
        let result = execute code'

        Assert.That( (result = 2) )

    [<Test>]
    member this.ifTest() =
        let e = parseProg """
            int n;

            fun int main() {
              n <- 2;
              if (n >= 1) { return 3; } else { return 100; }
            }
        """
        let code = 
            match run (genProg e) with
            | Result(code, _) ->
                code
            | Error(msg, _) ->
                failwith <| "code generation failed with error: " + msg

        let code' = resolve code
        let result = execute code'

        Assert.That( (result = 3) )  

    [<Test>]
    member this.funCall() =
        let e = parseProg """
            fun int callMe(int n) {
                if (n <= 0) { return 1; }
                else { return 2; }
            }

            fun int main() {
                int r;
                r <- callMe(3);
                return r;
            }
        """
        let code = 
            match run (genProg e) with
            | Result(code, _) ->
                code
            | Error(msg, _) ->
                failwith <| "code generation failed with error: " + msg

        let code' = resolve code
        let result = execute code'

        Assert.That( (result = 2) )  
    
    [<Test>]
    member this.factorial() =
        let e = parseProg """
            int n;

            fun int fac(int n) {
                if (n <= 0) { return 1; }
                else { return n * fac(n - 1); }
            }

            fun int main() {
              int r;
              n <- 4;
              r <- fac(n) + fac(n - 1);
              return r;
            }
        """
        let code = 
            match run (genProg e) with
            | Result(code, _) ->
                code
            | Error(msg, _) ->
                failwith <| "code generation failed with error: " + msg

        let code' = resolve code
        let result = execute code'

        Assert.That( (result = 30) )  

    [<Test>]
    member this.countDown() =
        let e = parseProg """
            fun int main() {
              int r;
              int n;
              n <- 5;
              r <- 1;
              while (n > 0) {
                r <- r * n;
                n <- n - 1;
              }
              return r;
            }
        """
        let code = 
            match run (genProg e) with
            | Result(code, _) ->
                code
            | Error(msg, _) ->
                failwith <| "code generation failed with error: " + msg

        let code' = resolve code
        let result = execute code'

        Assert.That( (result = 120) )         