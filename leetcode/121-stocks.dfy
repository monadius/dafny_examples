// function method {:opaque} Max(a: int, b: int): int
//   ensures a <= Max(a, b) && b <= Max(a, b)
//   ensures Max(a, b) == a || Max(a, b) == b
// {
//   if a >= b then a else b
// }

function method Max(a: int, b: int): int {
  if a >= b then a else b
}

predicate MaxProfitProp(xs: seq<int>, v: int) {
  forall i, j :: 0 <= i <= j < |xs| ==> xs[j] - xs[i] <= v
}

method MaxProfitSimple1(prices: array<int>) returns (profit: int)
  ensures MaxProfitProp(prices[..], profit)
{
  profit := 0;
  var i := 0;
  while i < prices.Length
    invariant forall u, v :: 0 <= u < i && u <= v < prices.Length ==> prices[v] - prices[u] <= profit
  {
    var j := i;
    while j < prices.Length 
      invariant i <= j <= prices.Length
      invariant forall u, v :: 0 <= u < i && u <= v < prices.Length ==> prices[v] - prices[u] <= profit
      invariant forall v :: i <= v < j ==> prices[v] - prices[i] <= profit
    {
      profit := Max(profit, prices[j] - prices[i]);
      j := j + 1;
    }
    i := i + 1;
  }
}

method MaxProfit1(prices: array<int>) returns (profit: int)
  requires 1 <= prices.Length
  ensures MaxProfitProp(prices[..], profit)
{
  var low := prices[0];
  profit := 0;
  var k := 0;

  while k < prices.Length
    invariant k <= prices.Length
    invariant forall i :: 0 <= i < k ==> prices[i] >= low
    invariant MaxProfitProp(prices[..k], profit)
  {
    if prices[k] < low {
      low := prices[k];
    }
    profit := Max(profit, prices[k] - low);
    k := k + 1;
  }
}

method MaxProfit2(prices: array<int>) returns (profit: int)
  requires 1 <= prices.Length
  ensures profit > 0 ==> exists i, j :: 0 <= i < prices.Length && i < j < prices.Length && profit == prices[j] - prices[i]
{
  var low := prices[0];
  profit := 0;
  var k := 0;
  ghost var lowIndex := 0;
  ghost var i, j := -1, -1;

  while k < prices.Length
    invariant k <= prices.Length
    invariant lowIndex == 0 || lowIndex < k
    invariant low == prices[lowIndex]
    invariant profit > 0 ==> 0 <= i < prices.Length && 0 <= j < prices.Length
    invariant profit > 0 ==> i < j
    invariant profit > 0 ==> profit == prices[j] - prices[i]
  {
    if prices[k] < low {
      low := prices[k];
      lowIndex := k;
    }
    if prices[k] - low > profit {
      i, j := lowIndex, k;
    }
    profit := Max(profit, prices[k] - low);
    k := k + 1;
  }
}

method MaxProfit(prices: array<int>) returns (profit: int)
  requires 1 <= prices.Length
  ensures forall i, j :: 0 <= i < prices.Length && i <= j < prices.Length ==> prices[j] - prices[i] <= profit
  ensures profit > 0 ==> exists i, j :: 0 <= i < prices.Length && i < j < prices.Length && profit == prices[j] - prices[i]
{
  var low := prices[0];
  profit := 0;
  var k := 0;
  ghost var lowIndex := 0;
  ghost var i, j := -1, -1;

  while k < prices.Length
    invariant k <= prices.Length
    invariant lowIndex == 0 || lowIndex < k
    invariant low == prices[lowIndex]
    invariant profit > 0 ==> 0 <= i < prices.Length && 0 <= j < prices.Length
    invariant profit > 0 ==> i < j
    invariant profit > 0 ==> profit == prices[j] - prices[i]
    invariant forall i :: 0 <= i < k ==> prices[i] >= low
    invariant MaxProfitProp(prices[..k], profit)
  {
    if prices[k] < low {
      low := prices[k];
      lowIndex := k;
    }
    if prices[k] - low > profit {
      i, j := lowIndex, k;
    }
    profit := Max(profit, prices[k] - low);
    k := k + 1;
  }
}