||| Towards a better Edda, which was good enough for a pandoc clone, but we can do better.

module Doc

import Decidable.Equality
import Data.String
import Data.List
import Data.List.Elem

namespace Pandoc

  data Inline
     = Period
     | Space
     | T String
     | B Inline
     | V String

  data Block
     = Empty
     | Para (List Inline)
     | Header Nat (List Inline)
     | Quote (List Inline)
     | Verb String


  record Meta where
    constructor M
    title  : List Inline
    author : List Inline
    date   : List Inline

  data Doc
     = Extract (List Block)
     | Standalone Meta (List Block)

  namespace Examples

    i1 : Inline
    i1 = T "Text"

    b1 : Block
    b1 = Para
       [ T "A"
       , Space
       , B $ T "simple"
       , Space
       , T "sentence"
       , Period
       , V "plus : (x,y : Nat) -> Nat"
       ]

    d1 : Doc
    d1 = Extract
       [ b1
       , Para [i1]
       , Verb "data Nat = Z | S Nat"
       ]

data Kind
   = DOC
   | BLOCK
   | INLINE
   | META

namespace Edda

  data Edda : (kind  : Kind) -> Type where
    Period, Space : Edda INLINE

    V : String -> Edda INLINE
    T : String -> Edda INLINE

    B : Edda INLINE -> Edda INLINE

    Empty : Edda BLOCK -> Edda BLOCK

    Para  : (text : List (Edda INLINE))
                 -> Edda BLOCK

    Verb : String -> Edda BLOCK

    Header : (level : Nat)
          -> (title : List (Edda INLINE))
                   -> Edda BLOCK

    Extract : (nodes : List (Edda BLOCK)) -> Edda DOC

    M : (title  : List (Edda INLINE))
     -> (author : List (Edda INLINE))
     -> (date   : List (Edda INLINE))
               -> Edda META

    Standalone : (mdata : Edda META)
              -> (body  : List (Edda BLOCK))
                       -> Edda DOC

namespace Edda2

  data Edda : (kind  : Kind) -> Type where
    Period, Space : Edda INLINE

    V : String -> Edda INLINE
    T : String -> Edda INLINE

    B : Edda INLINE -> Edda INLINE

    Empty : Edda BLOCK -> Edda BLOCK

    Para  : (text : List (Edda INLINE))
                 -> Edda BLOCK

    Verb : String -> Edda BLOCK

    Header : (level : Nat)
          -> (title : List (Edda INLINE))
          -> (body  : List (Edda BLOCK))
                   -> Edda BLOCK

    Extract : (nodes : List (Edda BLOCK)) -> Edda DOC

    M : (title  : List (Edda INLINE))
     -> (author : List (Edda INLINE))
     -> (date   : List (Edda INLINE))
               -> Edda META

    Standalone : (mdata : Edda META)
              -> (body  : List (Edda BLOCK))
                       -> Edda DOC

namespace Edda3

  data Edda : (kind  : Kind) -> Type -> Type where
    Period, Space : Edda INLINE a

    V : String -> Edda INLINE a
    C : a -> Edda INLINE a
    T : String -> Edda INLINE a

    B : Edda INLINE a -> Edda INLINE a

    Empty : Edda BLOCK a -> Edda BLOCK a

    Para  : (text : List (Edda INLINE a))
                 -> Edda BLOCK a

    Verb : String -> Edda BLOCK a
    Source : a -> Edda BLOCK a

    Header : (level : Nat)
          -> (title : List (Edda INLINE a))
          -> (body  : List (Edda BLOCK a))
                   -> Edda BLOCK a

    Extract : (nodes : List (Edda BLOCK a)) -> Edda DOC a

    M : (title  : List (Edda INLINE a))
     -> (author : List (Edda INLINE a))
     -> (date   : List (Edda INLINE a))
               -> Edda META a

    Standalone : (mdata : Edda META a)
              -> (body  : List (Edda BLOCK a))
                       -> Edda DOC a


data Hutton : List String -> Type where
  Z : Hutton xs
  S : (op : Hutton xs) -> Hutton xs
  P : (lop, rop : Hutton xs) -> Hutton xs

  V : (idx : Elem x xs)
          -> Hutton xs

  Let : (x     : String)
     -> (expr  : Hutton xs)
     -> (scope : Hutton (x::xs))
              -> Hutton xs

namespace Edda3

  namespace Examples

     sample : Hutton Nil
     sample = (Let "foo" (S Z) (P (V Here) (S Z)))

     v : Edda INLINE (Hutton Nil)
     v = C sample

     s : Edda DOC (Hutton Nil)
     s = Extract
         [ Para
           [ T "Here", Space, T "is", Space, T "an", Space, T "Example", Space, T "of", Space, T "a", Space, T "Hutton", Space, T "program", Period]
         , Source sample
         ]

     cheat : String -> List (Edda INLINE a)
     cheat = (intersperse Space . map T . words)

     s' : Edda DOC (Hutton Nil)
     s' = Extract
         [ Para
         $ cheat "Here is an example of a Hutton program" ++ [Period]
         , Source sample
         ]

namespace Edda4

  public export
  data Edda : (kind  : Kind) -> List Type -> Type where
    Period, Space : Edda INLINE as

    V : String -> Edda INLINE as
    C : Elem a as -> a -> Edda INLINE as
    T : String -> Edda INLINE as

    B : Edda INLINE as -> Edda INLINE as

    Empty : Edda BLOCK as

    Para  : (text : List (Edda INLINE as))
                 -> Edda BLOCK as

    Verb : String -> Edda BLOCK as
    Source : Elem a as -> a -> Edda BLOCK as

    Header : (level : Nat)
          -> (title : List (Edda INLINE as))
          -> (body  : List (Edda BLOCK  as))
                   -> Edda BLOCK as

    Extract : (nodes : List (Edda BLOCK as)) -> Edda DOC as

    M : (title  : List (Edda INLINE as))
     -> (author : List (Edda INLINE as))
     -> (date   : List (Edda INLINE as))
               -> Edda META as

    Standalone : (mdata : Edda META as)
              -> (body  : List (Edda BLOCK as))
                       -> Edda DOC as



  export
  foldLeft : (forall k . acc -> Edda k ts -> acc) -> acc -> Edda k ts -> acc

  foldLeft f x (B y)
    = f x y

  foldLeft f x (Para body)
    = foldl (foldLeft f) x body

  foldLeft f x (Header level title body)
    = foldl (foldLeft f) x body

  foldLeft f x (Extract nodes)
    = foldl (foldLeft f) x nodes

  foldLeft f x (Standalone mdata body)
    = foldl (foldLeft f) x body

  foldLeft f x y = f x y

  namespace Examples
     cheat : String -> List (Edda INLINE a)
     cheat = (intersperse Space . map T . words)

     sample : Hutton Nil
     sample = (Let "foo" (S Z) (P (V Here) (S Z)))

     public export
     s' : Edda DOC [(Hutton Nil), String]
     s' = Extract
         [ Para
         $ cheat "Here is an example of a Hutton program" ++ [Period]
         , Source Here sample
         , Para
         $ cheat "Here is an example of something else" ++ [ Period ]
         , Source (There Here)
           """
           (\\x:Nat.S x) Z
           """
         , Para
         $ cheat "Here is another example of a Hutton program"
           ++ [Period, Space, C Here sample]
         ]

     public export
     eg : Edda DOC [(Hutton Nil), String]
     eg = Extract
        [ Source Here sample
        , Para [T "Hehe"]
        , Source (There Here)
          """
          (\\x:Nat.S x) Z
          """
        , Para [C Here sample]
        ]


     cheat' : Elem a xs -> Elem b xs -> Bool
     cheat' Here Here = True
     cheat' Here (There x) = False
     cheat' (There x) Here = False
     cheat' (There x) (There y) = cheat' x y

     data ElemEQ : Elem x xs -> Elem y xs -> Type
       where
         Here : ElemEQ Here Here
         There : ElemEQ xs ys -> ElemEQ (There xs) (There ys)


     elemEQ_rhs_3 : ElemEQ Here (There z) -> Void
     elemEQ_rhs_3 Here impossible
     elemEQ_rhs_3 (There x) impossible

     elemEQ_rhs_2 : ElemEQ (There z) Here -> Void
     elemEQ_rhs_2 Here impossible
     elemEQ_rhs_2 (There x) impossible

     elemEQ_rhs_4_rhs_1 : (ElemEQ z w -> Void) -> ElemEQ (There z) (There w) -> Void
     elemEQ_rhs_4_rhs_1 f (There x) = f x

     elemEQ : (idx : Elem x xs) -> (idy : Elem y xs) -> Dec (ElemEQ idx idy)
     elemEQ Here Here = Yes Here
     elemEQ Here (There z) = No elemEQ_rhs_3
     elemEQ (There z) Here = No elemEQ_rhs_2
     elemEQ (There z) (There w) with (elemEQ z w)
       elemEQ (There z) (There w) | (Yes prf) = Yes (There prf)
       elemEQ (There z) (There w) | (No contra)
         = No (elemEQ_rhs_4_rhs_1 contra)

     prf : {idx : Elem x xs} -> {idy : Elem y xs} -> ElemEQ idx idy -> x = y
     prf Here = Refl
     prf (There z) = prf z

     export
     getX : Elem x xs -> List x -> Edda k xs -> List x
     getX y acc (C z w) with (elemEQ y z)
       getX y acc (C z w) | (Yes pf) with (prf pf)
         getX y acc (C z w) | (Yes pf) | Refl = acc ++ [w]
       getX y acc (C z w) | (No contra) = acc
     getX y acc (Source z w) with (elemEQ y z)
       getX y acc (Source z w) | (Yes pf) with (prf pf)
         getX y acc (Source z w) | (Yes pf) | Refl = acc ++ [w]
       getX y acc (Source z w) | (No contra) = acc
     getX _ acc _ = acc

--  data Saga : (kind  : Kind)
--           -> (level : Nat)
--           -> (type  : Type)
