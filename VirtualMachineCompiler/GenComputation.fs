module GenComputation

open FSharp.Text.Lexing

type Range = Position * Position

let noPos : Position = {
    pos_fname = ""
    pos_lnum = 0
    pos_bol = 0
    pos_cnum = 0
}

let noRange = (noPos, noPos)

type GenState = {
    /// the next smallest fresh symbolic address
    nextSymbolicAddr : int
}

type GenState with
    static member Empty =
        { nextSymbolicAddr = 0 }

type Outcome<'A> = 
    | Result of 'A * GenState
    | Error of string * Range

type Gen<'A> = GenState -> Outcome<'A>
        
type GenBuilder () =
    member x.Bind(comp : Gen<'A>, func : 'A -> Gen<'B>) : Gen<'B> =
        (fun genState -> 
            match comp genState with 
            | Result(a, s') -> func a s'
            | Error(msg, rng) -> Error(msg, rng) 
        )

    member x.Return(value : 'A) : Gen<'A> =
        (fun genState -> Result (value, genState))

    member x.Zero() : Gen<unit> =
        (fun genState -> Result ((), genState))

let gen = new GenBuilder()

let run (comp : Gen<'A>) : Outcome<'A> =
    comp { nextSymbolicAddr = 0 }

let error (msg : string) (rng : Range) (s : GenState) : Outcome<'A> =
    Error (msg, rng)

let getFreshSymbolicAddr (s : GenState) : Outcome<int> =
    Result (s.nextSymbolicAddr, { s with nextSymbolicAddr = s.nextSymbolicAddr + 1 })

let pass (s : GenState) : Outcome<unit> =
    Result ((), s)

let rec fold (init : 'S) (f : 'S -> 'A -> 'S) (l : List<Gen<'A>>) : Gen<'S> =
    match l with
    | fst :: rest ->
        gen {
            let! a = fst
            let! s = fold init f rest
            return (f s a)
        }
    | [] ->
        gen {
            return init
        }

let rec foldM (init : 'S) (f : 'S -> 'A -> Gen<'S>) (l : List<'A>) : Gen<'S> =
    match l with
    | first :: rest ->
        gen {
            let! s1 = f init first
            let! s2 = foldM s1 f rest
            return s2
        }
    | [] ->
        gen {
            return init
        }

let rec map (f : 'A -> 'B) (l : List<Gen<'A>>) : Gen<List<'B>> =
    match l with
    | fst :: rest ->
        gen {
            let! a = fst
            let! b = map f rest
            return (f a) :: b
        }
    | [] ->
        gen {
            return []
        }

let rec letAll (l : List<Gen<'A>>) : Gen<List<'A>> =
    match l with
    | fst :: rest ->
        gen {
            let! a = fst
            let! b = letAll rest
            return a :: b
        }
    | [] ->
        gen {
            return []
        }

let rec doAll (l : List<Gen<unit>>) : Gen<unit> =
    match l with
    | fst :: rest ->
        gen {
            do! fst
            do! doAll rest
            return ()
        }
    | [] ->
        gen {
            return ()
        }