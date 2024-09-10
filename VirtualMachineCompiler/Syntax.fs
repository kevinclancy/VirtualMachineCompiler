module Syntax

open Utils

type Ty =
    | Int
    | Array of elemTy : Ty * numElems : int * rng : Range
    | Struct of name : string * rng : Range
    | Ptr of ty : Ty * rng : Range

    with

        static member IsEqual (tyA : Ty) (tyB : Ty) : bool =
            match (tyA, tyB) with
            | Int, Int ->
                true
            | Array(elemTyA, numElemsA, _), Array(elemTyB, numElemsB, _) ->
                (Ty.IsEqual elemTyA elemTyB) && numElemsA = numElemsB
            | Struct(tyNameA, _), Struct(tyNameB, _) ->
                tyNameA = tyNameB
            | Ptr(tyA, _), Ptr(tyB, _) ->
                Ty.IsEqual tyA tyB
            | _, _ ->
                false

        member this.Size (tyEnv : TyEnv) : int =
            match this with
            | Int ->
                1
            | Ptr(_) ->
                1
            | Array(elemTy, numElems, _) ->
                (elemTy.Size tyEnv) * numElems
            | Struct(structName, _) ->
                let { name = _ ; fields = fields } = tyEnv[structName]
                List.sumBy (fun f -> f.ty.Size tyEnv) fields

and TyEnv = Map<string, TypeDef>

and VarDecl = {
    ty : Ty
    varName : string
    rng : Range
}

/// Definition of a struct type
and TypeDef = {
    name : string
    fields : List<VarDecl>
    rng : Range
}

    with

        member this.fieldOffset (tyEnv : TyEnv) (fieldName : string) =
            let ind = List.findIndex (fun d -> d.varName = fieldName) this.fields
            let fields_before, _ = List.splitAt ind this.fields
            List.sumBy (fun d -> d.ty.Size tyEnv) fields_before

type Expr =
    | FieldAccess of structExp : Expr * fieldName:string * Range
    | AddressOf of Expr * Range
    | Deref of Expr * Range
    | Plus of Expr * Expr * Range
    | Minus of Expr * Expr * Range
    | Times of Expr * Expr * Range
    | Eq of Expr * Expr * Range
    | Leq of Expr * Expr * Range
    | Geq of Expr * Expr * Range
    | Gt of Expr * Expr * Range
    | Lt of Expr * Expr * Range
    | Assign of lTarget : Expr * rSource : Expr * Range
    | Var of string * Range
    | IntLiteral of int * Range
    | FunCall of funName : string * args : List<Expr> * Range
    | New of Ty * Range

    with

        member this.Range =
            match this with
            | Plus(_,_,rng)
            | Minus(_,_,rng)
            | Times(_,_,rng)
            | Eq(_,_,rng)
            | Leq(_,_,rng)
            | Geq(_,_,rng)
            | Gt(_,_,rng)
            | Lt(_,_,rng)
            | FieldAccess(_, _, rng)
            | Assign(_,_,rng)
            | IntLiteral(_,rng)
            | Var(_,rng)
            | FunCall(_,_,rng)
            | New (_, rng) ->
                rng

type SwitchCase = {
    scrutineeValue : int
    statement : Stat
}

and Stat =
    | ExprStat of Expr * Range
    | IfThen of cond : Expr * thenClause : Stat * Range
    | IfThenElse of cond : Expr * thenClause : Stat * elseClause : Stat * Range
    | While of cond : Expr * body : Stat * Range
    | For of init : Stat * cond : Expr * incr : Stat * body : Stat * Range
    | Switch of cond : Expr * cases : List<SwitchCase> * deflt : Stat * Range
    | Sequence of stat1 : Stat * stat2 : Stat * Range
    | Return of returnExpr : Expr * Range
    | ReturnVoid of Range

type FunDecl = {
    name : string
    pars : List<VarDecl>
    retTy : Ty
    localDecls : List<VarDecl>
    body : Stat
}

type Prog = {
    typeDefs : List<TypeDef>
    globals : List<VarDecl>
    funDecls : List<FunDecl>
}