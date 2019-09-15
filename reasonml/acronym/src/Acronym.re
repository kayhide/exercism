let mconcat
    : array(string) => string
  = xs => Js.String.concatMany(xs, "");

let abbreviate = str =>
  str
  |> Js.String.splitByRe(Js.Re.fromString({|[ -]|}))
  |> Js.Array.map(Js.Option.getWithDefault(""))
  |> Js.Array.map(Js.String.charAt(0))
  |> mconcat
  |> Js.String.toUpperCase;
