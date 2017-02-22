- title : TDD in Idris 
- description : Introduction to TDD in Idris
- author : Marcin Wolicki
- theme : beige
- transition : default 

***


### Introduction to TDD in Idris

***

### Disclaimer

I am **not** an Idris developer. Still learning. Expect epic failer. 

Still should be fun.

***

### What is Idris?

- Pac-Man-complete functional programming language
- Haskell like syntax
- Eager (not lazy) evaluation
- Dependent types
- Interfaces (like type classes in Haskell)
- Totality checking
- Hols
- REPL

***

### IDE

- VIM
- Emacs
- and cool Atom

---

### Atom shortcuts
<table style="border: 1px solid white;">
    <tr><td>Typechecking</td><td>ctrl-alt-r</td></tr>
    <tr><td>Case-splitting</td><td>ctrl-alt-c</td></tr>
    <tr><td>Clause-adding</td><td>ctrl-alt-a</td></tr>
    <tr><td>Proof-search</td><td>ctrl-alt-s</td></tr>
    <tr><td>Showing the types of a variable</td><td>ctrl-alt-t</td></tr>
    <tr><td>Show the doc for a variable</td><td>ctrl-alt-d</td></tr>
    <tr><td>make-with</td><td>ctrl-alt-w</td></tr>
    <tr><td>make-case</td><td>ctrl-alt-m</td></tr>
    <tr><td>make-lemma</td><td>ctrl-alt-l</td></tr>
</table>

***


### DEMO

---

### Hello, World!

    [lang=haskell]
    module Main

    main : IO ()
    main = putStrLn "Hello, world!"

(yes, there is IO Monad!)


---

### Nat

    [lang=haskell]
    data Nat =
    Z
    | S Nat

####

    [lang=haskell]
    total 
    getVal : Nat -> Integer
    getVal Z = 0
    getVal (S val) = 1 + (getVal val)

    Show Nat where
    show x = show (getVal x)

---

### Vect

    [lang=haskell]
    data Vect : (len : Nat) -> (elem : Type) -> Type where
    Nil  : Vect Z elem
    (::) : (x : elem) -> (xs : Vect len elem) -> Vect (S len) elem

---

### swap
    [lang=haskell]
    total swap : (a,b) -> (b,a)
    swap (a, b) = (b, a)

---
### StringOrInt
    [lang=haskell]
    StringOrInt : Bool -> Type
    StringOrInt False = String
    StringOrInt True = Integer


---

### ZIP

    [lang=haskell]
    total
    myZip : Vect len t1 -> Vect len t2 -> Vect len (t1,t2)
    myZip [] [] = []
    myZip (x :: xs) (y :: ys) = (x,y) :: (zip xs ys)

### Take

    [lang=haskell]
    total 
    myTake : (Fin len) -> Vect len t1 -> t1
    myTake FZ (x :: _) = x
    myTake (FS pos) (x::xs) = myTake pos xs
---


### Interfaces

    [lang=haskell]
    interface Eq ty where
    (==) : ty -> ty -> Bool
    (/=) : ty -> ty -> Bool

    x /= y = not (x == y)
    x == y = not (x /= y)
 

---

### Vehicle

    [lang=haskell]
    data PowerSource = Pedal | Petrol

    data Vehicle : PowerSource -> Type where
    Bicycle : Vehicle Pedal
    Car : (fuel : Nat) -> Vehicle Petrol
    Bus : (fuel : Nat) -> Vehicle Petrol

####

    [lang=haskell]
    total refuel : Vehicle Petrol -> Vehicle Petrol
    refuel (Car fuel) = Car 40
    refuel (Bus fuel) = Bus 60
    refuel Bicycle impossible

---

### Format Types
 
    [lang=idris]
    data Format =
        FInt Format
        | FString Format
        | FOther Char Format
        | FEnd


    FormatType : Format -> Type
    FormatType FEnd = String
    FormatType (FOther _ xs) = (FormatType xs)
    FormatType (FInt xs) = Integer -> (FormatType xs)
    FormatType (FString xs) = String -> (FormatType xs)

---
### Format string

    getFormat : String -> Format
    getFormat s =
    getF (unpack s) where
        getF [] = FEnd
        getF ('%' :: 's' :: xs) = FString (getF xs)
        getF ('%' :: 'i' :: xs) = FInt (getF xs)
        getF (x :: xs) = FOther x (getF xs)

    fmt : (s:String) -> FormatType (getFormat s)
    fmt s = toFunction (getFormat s) "" where
        toFunction : (f:Format) -> String -> FormatType (f)
        toFunction FEnd acc = acc
        toFunction (FInt f) acc = \x => toFunction f (acc ++ show x)
        toFunction (FOther x f) acc = toFunction f (acc ++ singleton x)
        toFunction (FString f) acc = \x => toFunction f (acc ++ x)

---

### Safe div

    [lang=idris]
    safeDiv : (a:Int) -> (b: Int) -> {auto x: So (b/=0)} -> Int
    safeDiv a b = div a b


***

### Questions?