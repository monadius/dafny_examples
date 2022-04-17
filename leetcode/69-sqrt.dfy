method mySqrt(x: int) returns (res: int)
requires 0 <= x;
ensures res * res <= x && (res + 1) * (res + 1) > x;
{
    var l, r := 0, x;
    while (l <= r)
    decreases r - l;
    invariant l >= 0;
    invariant r >= 0;
    invariant l*l <= x;
    invariant (r+1)*(r+1) > x;
    {
        var mid := (l + r) / 2;
        if (mid * mid <= x && (mid + 1) * (mid + 1) > x) {
            return mid;
        } else if (mid * mid <= x) {
            l := mid + 1;
        } else {
            r := mid - 1;
        }
    }
}