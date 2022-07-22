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
        let ty, code = 
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
        let ty, code = 
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

    //[<Test>]
    //member this.ifStat() =
    //    let e = parseExpr "x <- 2 ; if (3 > 2) { x <- 6 }"
    //    let ty, code = 
    //        match run (genExprR Context.empty e) with
    //        | Result(code, _) ->
    //            code
    //        | Error(_, _) ->
    //            failwith "code generation failed"

    //    match ty with
    //    | Int(_) ->
    //        ()
    //    | _ ->
    //        failwith "expected type of '3 + 2' to be int"

    //    let code' = List.concat [code ; [Halt]]
    //    let code'' = resolve code'
    //    let result = execute code''

    //    Assert.That( (result = 24) )        


