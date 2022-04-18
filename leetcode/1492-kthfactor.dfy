include "../lib/Factors.dfy"

import opened FactorsModule

method KthFactor(n: int, k: int) returns (r: int)
  requires 0 < k <= n;
  ensures r == -1 <==> k > |AllFactors(n)|
  ensures r > 0 <==> k <= |AllFactors(n)| && AllFactors(n)[k - 1] == r
{
  ghost var factors := [];
  var i := 1;
  var cnt := k;
  r := -1;
  
  while (i <= n)
    invariant i <= n + 1
    invariant factors == Factors(n, i - 1)
    invariant k - cnt == |factors|
  {
      if (n % i == 0) {
          cnt := cnt - 1;
          factors := factors + [i];
      }
      if (cnt == 0) {
          r := i;
          break;
      }
      i := i + 1;
  }
  if i <= n {
    FactorsPrefix(n, i, n);
  }
}
