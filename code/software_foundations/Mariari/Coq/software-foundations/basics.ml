open Nat

type day =
| Coq_monday
| Coq_tuesday
| Coq_wednesday
| Coq_thursday
| Coq_friday
| Coq_saturday
| Coq_sunday

(** val day_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> day -> 'a1 **)

let day_rect f f0 f1 f2 f3 f4 f5 = function
| Coq_monday -> f
| Coq_tuesday -> f0
| Coq_wednesday -> f1
| Coq_thursday -> f2
| Coq_friday -> f3
| Coq_saturday -> f4
| Coq_sunday -> f5

(** val day_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> day -> 'a1 **)

let day_rec f f0 f1 f2 f3 f4 f5 = function
| Coq_monday -> f
| Coq_tuesday -> f0
| Coq_wednesday -> f1
| Coq_thursday -> f2
| Coq_friday -> f3
| Coq_saturday -> f4
| Coq_sunday -> f5

(** val next_weekday : day -> day **)

let next_weekday = function
| Coq_monday -> Coq_tuesday
| Coq_tuesday -> Coq_friday
| Coq_wednesday -> Coq_thursday
| Coq_thursday -> Coq_friday
| _ -> Coq_monday

type bool =
| Coq_true
| Coq_false

(** val bool_rect : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rect f f0 = function
| Coq_true -> f
| Coq_false -> f0

(** val bool_rec : 'a1 -> 'a1 -> bool -> 'a1 **)

let bool_rec f f0 = function
| Coq_true -> f
| Coq_false -> f0

(** val negb : bool -> bool **)

let negb = function
| Coq_true -> Coq_false
| Coq_false -> Coq_true

(** val andb : bool -> bool -> bool **)

let andb b1 b2 =
  match b1 with
  | Coq_true -> b2
  | Coq_false -> Coq_false

(** val orb : bool -> bool -> bool **)

let orb b1 b2 =
  match b1 with
  | Coq_true -> Coq_true
  | Coq_false -> b2

(** val nandb : bool -> bool -> bool **)

let nandb b1 b2 =
  negb (andb b1 b2)

type rgb =
| Coq_red
| Coq_green
| Coq_blue

(** val rgb_rect : 'a1 -> 'a1 -> 'a1 -> rgb -> 'a1 **)

let rgb_rect f f0 f1 = function
| Coq_red -> f
| Coq_green -> f0
| Coq_blue -> f1

(** val rgb_rec : 'a1 -> 'a1 -> 'a1 -> rgb -> 'a1 **)

let rgb_rec f f0 f1 = function
| Coq_red -> f
| Coq_green -> f0
| Coq_blue -> f1

type color =
| Coq_black
| Coq_white
| Coq_primary of rgb

(** val color_rect : 'a1 -> 'a1 -> (rgb -> 'a1) -> color -> 'a1 **)

let color_rect f f0 f1 = function
| Coq_black -> f
| Coq_white -> f0
| Coq_primary x -> f1 x

(** val color_rec : 'a1 -> 'a1 -> (rgb -> 'a1) -> color -> 'a1 **)

let color_rec f f0 f1 = function
| Coq_black -> f
| Coq_white -> f0
| Coq_primary x -> f1 x

(** val monochrome : color -> bool **)

let monochrome = function
| Coq_primary _ -> Coq_false
| _ -> Coq_true

(** val evenb : Z.t -> bool **)

let rec evenb n =
  (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
    (fun _ -> Coq_true)
    (fun n0 -> (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
                 (fun _ -> Coq_false)
                 (fun n' -> evenb n')
                 n0)
    n

(** val mult : Z.t -> Z.t -> Z.t **)

let rec mult n m =
  (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
    (fun _ -> Z.zero)
    (fun n' -> add m (mult n' m))
    n

(** val factorial : Z.t -> Z.t **)

let rec factorial n =
  (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
    (fun _ -> Z.succ Z.zero)
    (fun n' -> mul n (factorial n'))
    n

(** val eqb : Z.t -> Z.t -> bool **)

let rec eqb n m =
  (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
    (fun _ -> (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
                (fun _ -> Coq_true)
                (fun _ -> Coq_false)
                m)
    (fun n' -> (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
                 (fun _ -> Coq_false)
                 (fun m' -> eqb n' m')
                 m)
    n

(** val leb : Z.t -> Z.t -> bool **)

let rec leb n m =
  (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
    (fun _ -> Coq_true)
    (fun n' -> (fun f0 fs n -> if n = Z.zero then f0 () else fs (n-1))
                 (fun _ -> Coq_false)
                 (fun m' -> leb n' m')
                 m)
    n

(** val ltb : Z.t -> Z.t -> bool **)

let ltb n m =
  leb (Z.succ n) m
