let abbreviate = str =>
  str
  |> Js.String.splitByRe(Js.Re.fromString({|[ -]|}))
  |> Js.Array.map(Js.Option.getWithDefault(""))
  |> Js.Array.map(Js.String.charAt(0))
  |> Js.Array.joinWith("")
  |> Js.String.toUpperCase;
