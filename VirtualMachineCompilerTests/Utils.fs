module Utils

open NUnit.Framework
open FSharp.Text.Lexing
open Syntax

let expect (cond : bool) =
    Assert.That(cond)

let parseStat (s : string) : Stat =
    let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(s)
    Parser.stat (Lexer.token) lexbuffer    

let parseExpr (s : string) : Expr =
    let lexbuffer : LexBuffer<char> = LexBuffer<char>.FromString(s)
    Parser.expr (Lexer.token) lexbuffer      