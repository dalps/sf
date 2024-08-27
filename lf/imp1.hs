module Imp1 where

import qualified Prelude

data Bool =
   True
 | False

andb :: Bool -> Bool -> Bool
andb b1 b2 =
  case b1 of {
   True -> b2;
   False -> False}

negb :: Bool -> Bool
negb b =
  case b of {
   True -> False;
   False -> True}

data Nat =
   O
 | S Nat

data Option a =
   Some a
 | None

eqb :: Bool -> Bool -> Bool
eqb b1 b2 =
  case b1 of {
   True -> b2;
   False -> case b2 of {
             True -> False;
             False -> True}}

add :: Nat -> Nat -> Nat
add n m =
  case n of {
   O -> m;
   S p -> S (add p m)}

mul :: Nat -> Nat -> Nat
mul n m =
  case n of {
   O -> O;
   S p -> add m (mul p m)}

sub :: Nat -> Nat -> Nat
sub n m =
  case n of {
   O -> n;
   S k -> case m of {
           O -> n;
           S l -> sub k l}}

eqb0 :: Nat -> Nat -> Bool
eqb0 n m =
  case n of {
   O -> case m of {
         O -> True;
         S _ -> False};
   S n' -> case m of {
            O -> False;
            S m' -> eqb0 n' m'}}

leb :: Nat -> Nat -> Bool
leb n m =
  case n of {
   O -> True;
   S n' -> case m of {
            O -> False;
            S m' -> leb n' m'}}

data Ascii0 =
   Ascii Bool Bool Bool Bool Bool Bool Bool Bool

eqb1 :: Ascii0 -> Ascii0 -> Bool
eqb1 a b =
  case a of {
   Ascii a0 a1 a2 a3 a4 a5 a6 a7 ->
    case b of {
     Ascii b0 b1 b2 b3 b4 b5 b6 b7 ->
      case case case case case case case eqb a0 b0 of {
                                     True -> eqb a1 b1;
                                     False -> False} of {
                                True -> eqb a2 b2;
                                False -> False} of {
                           True -> eqb a3 b3;
                           False -> False} of {
                      True -> eqb a4 b4;
                      False -> False} of {
                 True -> eqb a5 b5;
                 False -> False} of {
            True -> eqb a6 b6;
            False -> False} of {
       True -> eqb a7 b7;
       False -> False}}}

data String =
   EmptyString
 | String0 Ascii0 String

eqb2 :: String -> String -> Bool
eqb2 s1 s2 =
  case s1 of {
   EmptyString -> case s2 of {
                   EmptyString -> True;
                   String0 _ _ -> False};
   String0 c1 s1' ->
    case s2 of {
     EmptyString -> False;
     String0 c2 s2' ->
      case eqb1 c1 c2 of {
       True -> eqb2 s1' s2';
       False -> False}}}

type Total_map a = String -> a

t_update :: (Total_map a1) -> String -> a1 -> String -> a1
t_update m x v x' =
  case eqb2 x x' of {
   True -> v;
   False -> m x'}

type State = Total_map Nat

data Aexp =
   ANum Nat
 | AId String
 | APlus Aexp Aexp
 | AMinus Aexp Aexp
 | AMult Aexp Aexp

data Bexp =
   BTrue
 | BFalse
 | BEq Aexp Aexp
 | BNeq Aexp Aexp
 | BLe Aexp Aexp
 | BGt Aexp Aexp
 | BNot Bexp
 | BAnd Bexp Bexp

aeval :: State -> Aexp -> Nat
aeval st a =
  case a of {
   ANum n -> n;
   AId x -> st x;
   APlus a1 a2 -> add (aeval st a1) (aeval st a2);
   AMinus a1 a2 -> sub (aeval st a1) (aeval st a2);
   AMult a1 a2 -> mul (aeval st a1) (aeval st a2)}

beval :: State -> Bexp -> Bool
beval st b =
  case b of {
   BTrue -> True;
   BFalse -> False;
   BEq a1 a2 -> eqb0 (aeval st a1) (aeval st a2);
   BNeq a1 a2 -> negb (eqb0 (aeval st a1) (aeval st a2));
   BLe a1 a2 -> leb (aeval st a1) (aeval st a2);
   BGt a1 a2 -> negb (leb (aeval st a1) (aeval st a2));
   BNot b1 -> negb (beval st b1);
   BAnd b1 b2 -> andb (beval st b1) (beval st b2)}

data Com =
   CSkip
 | CAsgn String Aexp
 | CSeq Com Com
 | CIf Bexp Com Com
 | CWhile Bexp Com

ceval_step :: State -> Com -> Nat -> Option State
ceval_step st c i =
  case i of {
   O -> None;
   S i' ->
    case c of {
     CSkip -> Some st;
     CAsgn l a1 -> Some (t_update st l (aeval st a1));
     CSeq c1 c2 ->
      case ceval_step st c1 i' of {
       Some st' -> ceval_step st' c2 i';
       None -> None};
     CIf b c1 c2 ->
      case beval st b of {
       True -> ceval_step st c1 i';
       False -> ceval_step st c2 i'};
     CWhile b1 c1 ->
      case beval st b1 of {
       True ->
        case ceval_step st c1 i' of {
         Some st' -> ceval_step st' c i';
         None -> None};
       False -> Some st}}}

