type planet =
  | Mercury
  | Venus
  | Earth
  | Mars
  | Jupiter
  | Saturn
  | Neptune
  | Uranus;

let ageOnEarth = x => x /. 31557600.0;

let ageOn = (planet, x) =>
  switch planet {
  | Mercury => x /. 0.2408467 |> ageOnEarth
  | Venus => x /. 0.61519726 |> ageOnEarth
  | Earth => x |> ageOnEarth
  | Mars => x /. 1.8808158 |> ageOnEarth
  | Jupiter => x /. 11.862615 |> ageOnEarth
  | Saturn => x /. 29.447498 |> ageOnEarth
  | Uranus => x /. 84.016846 |> ageOnEarth
  | Neptune => x /. 164.79132 |> ageOnEarth
  };
