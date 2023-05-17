module Random {
  method random(a: int, b: int) returns (r: int)
    requires a <= b
    ensures a <= r <= b
}

function rand(n: int): int
  requires 0 <= n
  ensures 0 <= rand(n) <= n

method rand2(n: int) returns (r: int)
  requires 0 <= n
  ensures 0 <= r <= n

method Main()
{
  var x := 2;
  var y := 4;

  var r1 := Random.random(x, y);
  var r2 := Random.random(x, y);

  assert r1 <= 4 && r2 <= 4;

  r1 := rand(y);
  r2 := rand(y);

  assert r1 <= 4 && r2 <= 4;
  assert r1 == r2;

  r1 := rand2(y);
  r2 := rand2(y);

  assert r1 <= 4 && r2 <= 4;
  // Wrong:
  //assert r1 == r2;
}
