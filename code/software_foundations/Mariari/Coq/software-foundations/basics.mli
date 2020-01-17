open Nat

type day =
| Coq_monday
| Coq_tuesday
| Coq_wednesday
| Coq_thursday
| Coq_friday
| Coq_saturday
| Coq_sunday

val day_rect : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> day -> 'a1

val day_rec : 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> 'a1 -> day -> 'a1

val next_weekday : day -> day

type bool =
| Coq_true
| Coq_false

val bool_rect : 'a1 -> 'a1 -> bool -> 'a1

val bool_rec : 'a1 -> 'a1 -> bool -> 'a1

val negb : bool -> bool

val andb : bool -> bool -> bool

val orb : bool -> bool -> bool

val nandb : bool -> bool -> bool

type rgb =
| Coq_red
| Coq_green
| Coq_blue

val rgb_rect : 'a1 -> 'a1 -> 'a1 -> rgb -> 'a1

val rgb_rec : 'a1 -> 'a1 -> 'a1 -> rgb -> 'a1

type color =
| Coq_black
| Coq_white
| Coq_primary of rgb

val color_rect : 'a1 -> 'a1 -> (rgb -> 'a1) -> color -> 'a1

val color_rec : 'a1 -> 'a1 -> (rgb -> 'a1) -> color -> 'a1

val monochrome : color -> bool

val evenb : Z.t -> bool

val mult : Z.t -> Z.t -> Z.t

val factorial : Z.t -> Z.t

val eqb : Z.t -> Z.t -> bool

val leb : Z.t -> Z.t -> bool

val ltb : Z.t -> Z.t -> bool
