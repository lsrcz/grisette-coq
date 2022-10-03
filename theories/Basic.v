Definition is_some {a} (o : option a) :=
  match o with
  | Some _ => True
  | None => False
  end.

#[global] Hint Unfold is_some : core.

