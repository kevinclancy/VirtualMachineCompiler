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
    member this.switchTest() =
        let e = parseProg """
            fun int main() {
              int r;
              int n;
              n <- 3;
              r <- 0;
              while (n >= 0) {
                switch(n) {
                  case 0:
                    r <- r * 2;
                    break;
                  case 1:
                    r <- r + 2;
                    break;
                  case 2:
                    r <- r + 1;
                    break;
                  default:
                    r <- r + 1;
                    break;
                }
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

        Assert.That( (result = 8) )

    [<Test>]
    member this.badStructDef () =
        let e = parseProg """
            typedef struct Vec { int x; int y; };

            fun int main() {
                struct Point pos;
                return 0;
            }
        """
        match run (genProg e) with
        | Result(code, _) ->
            failwith "Type-checking should fail since type Point is not defined"
        | Error(msg, _) ->
            Assert.That ( msg.Contains("type Point not defined") )
            ()

    [<Test>]
    member this.structDef () =
        let e = parseProg """
            typedef struct Vec { int x; int y; };

            fun int main() {
                struct Vec pos;
                return 0;
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

        Assert.That( (result = 0) )

    [<Test>]
    member this.structFieldAccess () =
        let e = parseProg """
            typedef struct Vec { int x; int y; };

            fun int main() {
                struct Vec pos;
                pos.x <- 2;
                return pos.x;
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
    member this.structAssign () =
        let e = parseProg """
            typedef struct Vec { int x; int y; };

            fun int main() {
                struct Vec pos1;
                struct Vec pos2;
                pos1.x <- 2;
                pos1.y <- 3;
                pos2 <- pos1;
                return pos2.y;
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
    member this.structReturn () =
        let e = parseProg """
            typedef struct Vec { int x; int y; };

            fun struct Vec getPos() {
                struct Vec pos;
                pos.x <- 1;
                pos.y <- 2;
                return pos;
            }

            fun int main() {
                struct Vec pos;
                pos <- getPos();
                return pos.x;
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

        Assert.That( (result = 1) )

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