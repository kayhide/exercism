let isLeapYear = n =>
  switch (n mod 400, n mod 100, n mod 4) {
  | (0, _, _) => true
  | (_, 0, _) => false
  | (_, _, 0) => true
  | _ => false
  };
