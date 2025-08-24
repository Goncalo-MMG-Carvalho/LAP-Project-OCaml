(* Maze module body *)
(* LAP (AMD 2023) *)

(* 
Student 1: 61626 - Augusto Mateus
Student 2: 61605 - Goncalo Carvalho

Comment: We Completed the project
*)

(*
0123456789012345678901234567890123456789012345678901234567890123456789012345678901234567890123456789
	100 columns
*)


(* COMPILATION - How Mooshak builds this module:
		ocamlc -c Maze.mli Maze.ml
*)



(* AUXILIARY GENERAL FUNCTIONS - you can add more *)

(* Sorted lists with no repetitions *)
(* precondition for all the list arguments:
		isCanonical l && isCanonical l1 && isCanonical l2 *)
(* postcondition for all the list results: isCanonical result *)


(* Do Prof *)
let rec removeDups z = (* pre: z sorted *)
  match z with
  | [] -> []
  | [x] -> [x]
  | x::y::xs -> (if x = y then [] else [x])@ removeDups (y::xs)
;;

let canonize z = (* sort and remove duplicates *)
  removeDups (List.sort compare z)
;;

let isCanonical z = (* check if sorted and with no duplicates *)
  z = (canonize z)
;; 

let belongs v l =
  List.mem v l
;;

let length =
  List.length
;;

let filter =
  List.filter
;;

let exists =
  List.exists
;;

let for_all =
  List.for_all
;;

let partition =
  List.partition
;;

let contained l1 l2 =
  for_all (fun x -> belongs x l2) l1
;;

let union l1 l2 =
  canonize (l1@l2)

let inter l1 l2 =
  filter (fun x -> belongs x l2) l1
;;

let diff l1 l2 =
  filter (fun a -> not (belongs a l2)) l1
;;

let map f l =
  canonize (List.map f l)
;;

let merge l =
  canonize (List.flatten l)
;;

let flatMap f l =
  merge (List.map f l)
;;

let showi l =
  let li = List.map string_of_int l in
  let body = String.concat "," li in
  Printf.printf "[%s]\n" body
;;

let showp l =
  let li = List.map (fun (a,b) -> Printf.sprintf "(%d,%d)" a b) l in
  let body = String.concat "," li in
  Printf.printf "[%s]\n" body
;;


(* TYPES & CONSTANTS *)

type room = int
type rooms = room list

type path = room list
type island = room list

type passage = room * room
type passages = passage list

type maze = {
  rooms: rooms;
  entrances: rooms;
  exits: rooms;
  passages: passages
}

let _NO_PATH = []


(* SOME EXAMPLES - you can add more *)

let myMaze = {
  rooms = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13];
  entrances = [1;4;11];
  exits = [6;12];
  passages = [(1,2);(1,4);(1,5);(2,5);(3,6);(4,5);(4,7);
              (5,6);(5,8);(6,9);(7,8);(8,9);(10,11);(11,12)]
};;

let loopMaze = {
  rooms = [1;2;3;4];
  entrances = [1];
  exits = [4];
  passages = [(1,2);(2,3);(3,4);(4,1)]
};;

(* ----------------------------- Our AUX -----------------------------------*)



let rec getSecondsOfPairList l n = 
  match l with
  |[]        -> [] 
  |(x,y)::ps -> 
      if x = n 
      then union [y] (getSecondsOfPairList ps n) 
      else getSecondsOfPairList ps n
;;

let rec getFirstsOfPairList l n = 
  match l with
  |[]        -> [] 
  |(x,y)::ps -> 
      if y = n 
      then union [x] (getFirstsOfPairList ps n) 
      else getFirstsOfPairList ps n
;; 

let isExit m r = 
  (belongs r (m.exits)) 
;;

let rec listFromTo a b = 
  if a < b then a::listFromTo (a+1) b
  else [b] 
;;

let rec pairsFromTo a b =
  if a < b then (a,a+1) :: pairsFromTo (a+1) b
  else []
  
;;

(* FUNCTION isValid *)

let isValid m = 
  for_all (fun x -> x>=0) m.rooms &&
  m.rooms <> [] &&
  m.entrances <> [] &&
  isCanonical m.rooms &&
  isCanonical m.entrances &&
  isCanonical m.exits && 
  isCanonical m.passages &&
  for_all (fun (x,y) -> belongs x m.rooms && belongs y m.rooms ) m.passages &&
  contained m.exits m.rooms &&
  contained m.entrances m.rooms &&
  not (exists (fun x -> belongs x m.exits) m.entrances) 
;;

(* FUNCTION makeLineMaze *)

let rec makeLineMaze a b = 
  {
    rooms = listFromTo a b;
    entrances = [a];
    exits = [b];
    passages = pairsFromTo a b
  } 
;;


(* FUNCTION combine *)

let combine m1 m2 = 
  let entr = union m1.entrances m2.entrances in
  let ex = diff (union m1.exits m2.exits) entr   in 
  
  {
    rooms = union m1.rooms m2.rooms;
    entrances = entr;
    exits =  ex;
    passages = union m1.passages m2.passages
  } 
;;

(* FUNCTION next *)

let next m r = 
  getSecondsOfPairList m.passages r

;;

let isLeaf m r =
  next m r = []
;; 

(* FUNCTION next2 *)

let rec next2 m rs = 
  match rs with
  |[]    -> []
  |x::xs -> union (next m x) (next2 m xs)
;;

(* FUNCTION prev *)

let prev m r = 
  getFirstsOfPairList m.passages r
;;

(* FUNCTION adjacent *)

let adjacent m r = 
  union (next m r) (prev m r)
;;


(* FUNCTION reachable *) 

let rec reachable m = 
  reachableSupport m (union m.entrances (next2 m m.entrances)) 
     
and 
  reachableSupport m rs =
  let a = union rs (next2 m rs) in
  if a = rs (* (contained a rs) if the list weren't sorted, but they are *)
  then rs (* if the reached rooms dont have next rooms then 'return' the reached *)
  else reachableSupport m a (* else try to reach further *)
;;

(* FUNCTION solitary *)

let rec solitary m = 
  solitarySupport m m.rooms
  
and
  solitarySupport m l =
  match l with
  |[]    -> []
  |x::xs -> if (adjacent m x) = [] then union [x] (solitarySupport m xs)
      else solitarySupport m xs
;;

(* FUNCTION islands *) 

let rec islands m =
  applyIslandsSup m m.rooms
    
and
  applyIslandsSup m rl =
  match rl with
  |[] -> []
  |r::rs -> let a = islandsSup m [r] in
      union [a] (applyIslandsSup m (dontBelong rl a)) 
      (*joins the island a to the other islands,
         the other islands are obtain by ignoring the elements already on the island a *)
  
and 
  islandsSup m rl = (* Gives the island rl belongs to, usually starts with just one room *)
  let a = adjacent2Islands m rl in 
  if a = adjacent2Islands m a 
  then a
  else islandsSup m a
  
and
  dontBelong l1 l2 = (* give the elems from l1 that doesnt belong to l2*)
  filter (fun x -> not (belongs x l2)) l1
    
and
  adjacent2Islands m rs = 
  match rs with
  |[]    -> [] 
  |x::xs -> union [x] (union (adjacent m x) (adjacent2Islands m xs))
;; 

(* FUNCTION paths *)

let rec paths m = 
  (* applies explore to the entrances of the maze *)
  applyExplore m m.entrances
  
and (* gives all the paths possible starting from the rooms on list l*)
  applyExplore m l =
  match l with
  |[] -> []
  |x::xs -> union (explore m [x] (next m x)) (applyExplore m xs)
  
and (* gives all the paths possible starting from the sequence of rooms on list prev *)
  explore m prev lst  = 
  match lst with
  |[]    -> [] 
  |r::rs -> let nextPrev = union prev [r] in
  (* if it's a leaf there are no further paths to be taken starting from prev*)
      if isLeaf m r 
      then [nextPrev] 
      else 
        (* if it's an exit then this path is complete, 
but there may be other paths further ahead *)
      if isExit m r 
      then union [nextPrev] (union (explore m nextPrev (next m r)) (explore m prev rs))
          (* if it's neither then proceed as normal *)
      else union (explore m nextPrev (next m r)) (explore m prev rs)
;;

(* FUNCTION shortest *)

(*Since we are trying to find the shortest path we will make use of the function paths
and select the shortest from there that leads us to an exit*)
let rec shortest m = 
  shortestSup m (paths m)

and 
  shortestSup m lp (* lp is a list of possible paths *) = 
  match lp with
  |[]     -> _NO_PATH 
  |p::lps -> let lowest = shortestSup m lps in let lowestLen = length lowest in
      if (length p < lowestLen || lowestLen = 0 || lowestLen = 1) 
      && exists (fun y -> belongs y m.exits) p
      (* if length is invalid (0 or 1) or if it is lower than 
        the lowest of the rest then this is the lowest of all *)
      then p 
      else lowest (* else the lowest of the rest is the lowest  *)
;;


(* FUNCTION hasLoop *)

let rec hasLoop m = 
  applyExploreLoop m m.rooms
    
and 
  applyExploreLoop m l =
  match l with
  |[]    -> false
  |x::xs -> (exploreLoop m [x] (next m x)) || (applyExploreLoop m xs)
  
and 
  exploreLoop m prev lst  = (*check if the room/list of rooms prev leads to a loop*)
  match lst with
  |[]    -> false
  |r::rs -> if belongs r prev then true
      else (exploreLoop m (union prev [r]) (next m r)) || (exploreLoop m prev rs)
;; 


(* FUNCTION shortest2 *)

let rec pathsWLoops m = 
  (* Gives only the paths that lead to an exit,
  and doesn´t go further then the first exit it finds *)
  applyExploreWLoops m m.entrances
  
and (* gives all the paths,that satisfy, starting from the rooms on list l*)
  applyExploreWLoops m l =
  match l with
  |[] -> _NO_PATH
  |x::xs -> union (exploreWLoops m [x] (next m x)) (applyExploreWLoops m xs)
  
and (* gives all the paths possible starting from the sequence of rooms on list prev 
    and that end at an exit without continuing after finding the first exit*)
  exploreWLoops m prev lst  = 
  match lst with
  |[]    -> _NO_PATH 
  |r::rs -> let nextPrev = union prev [r] in
      if isExit m r then [nextPrev]  
  (*if it is an exit then it's the shortest path to an exit starting from prev *) 
  
   (* if r is a leaf there are no further paths to be taken starting from prev;
if r belongs to prev then it's a loop, stop there is no exit;*) 
      else if isLeaf m r || belongs r prev then []
      (* if it's none then proceed as normal *)
      else union (exploreWLoops m nextPrev (next m r)) (exploreWLoops m prev rs)
;;

let rec shortest2 m = 
  if not (hasLoop m) then shortest m
  else 
    shortestSup m (pathsWLoops m) 
;;

let myMaze = {
  rooms = [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13];
  entrances = [1;4;11];
  exits = [6;12];
  passages = [(1,2);(1,4);(1,5);(2,5);(3,6);(4,5);(4,7);
              (5,6);(5,8);(6,9);(7,8);(8,9);(10,11);(11,12)]
};;