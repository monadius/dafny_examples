include "../lib/math/Factors.dfy"

import opened FactorsModule

method KthFactor(n: int, k: int) returns (r: int)
  requires 0 < k <= n;
  ensures r == -1 <==> k > |AllFactors(n)|
  ensures r > 0 <==> k <= |AllFactors(n)| && AllFactors(n)[k - 1] == r
{
  ghost var factors := [];
  var d := 1;
  var cnt := 0;
  r := -1;
  
  while d <= n
    invariant d <= n + 1
    invariant factors == Factors(n, d - 1)
    invariant cnt == |factors|
    invariant cnt < k
  {
      if (n % d == 0) {
          cnt := cnt + 1;
          factors := factors + [d];
          if cnt == k {
            r := d;
            break;
          }
      }
      d := d + 1;
  }
  if d <= n {
    FactorsPrefix(n, d, n);
  }
}
