module TargetCode

type Instruction =
    // not a real instruction.
    /// SymbolicAddress(n) means that the following instruction is located at symbolic address n
    | SymbolicAddress of int
    // real instructions below
    | Halt
    | Mul
    | Add
    | Sub
    | Pop
    | Leq
    | Eq
    | Geq
    | Lt
    | Neg
    | Dup
    | New
    | Mark
    | Call
    /// Slides a chunk of memory from the top of the stack downward
    /// slideDistance - the amount of times to slide the return segment downward by one word
    /// numWordsToSlide - the number of words comprising the return segment
    | Slide of slideDistance : int * numWordsToSlide : int
    /// Push numWords new words to the top of the stack; their values are arbitrary
    | Alloc of numWords : int
    /// Reassigns EP so that maxWords words occur between the SP and the EP,
    /// throwing an exception if there isn't enough space
    | Enter of maxWords : int
    /// Returns from function: recovers EP and FP registers, removes extra words above return value, and jumps back to caller
    | Return of wordsToRemove : int 
    /// Pops the address n off the stack and pushes the words stored at n,n+1,...,n+(numWords-1)
    | Load of numWords : int
    /// pushes constantToLoad onto the stack
    | LoadC of constantToLoad : int
    /// pushes (*FP + offset) onto the stack
    | LoadRC of offset : int
    /// "loadrc offset" followed by "load numWords"
    | LoadR of offset : int * numWords : int
    /// numWords cells below the top of the stack are stored to the address at the top of the stack and subsequent addresses
    | Store of numWords : int
    /// "loadrc offset" followed by "store numWords"
    | StoreR of offset : int * numWords : int
    // jump to destAddr 
    | Jump of destAddr : int
    // jump to destAddr if top of stack is 0, pop top of stack
    | JumpZ of destAddr : int
    // pop an index off the top of the stack. then jump to (baseAddr + index).
    | JumpI of baseAddr : int