predicate distinct(s: string, i: int, j: int) {
    forall p, q :: i <= p < q <= j && 0 <= i <= j < |s| ==> s[p] != s[q]
}

function method max(x: int, y: int) : int {
    if x > y then x else y
}

lemma distinctSingleton(s: string, i: int, j: int)
requires |s| == 1
ensures distinct(s, i, j)
{}

method lengthOfLongestSubstring(s: string) returns (r: int)
//ensures forall i, j :: distinct(s, i, j) && 0 <= i <= j < |s| ==> r >= j - i + 1;  
{
    var last : map<char, int> := map[];
    var maxL, left := 1, 0;
    var i := 0;
    while i < |s|
    decreases |s| - i;
    invariant 0 <= i <= |s|;
    invariant forall j :: 0 <= j < i && distinct(s, j, i-1) ==> left <= j;
    invariant distinct(s, left, i-1);
    invariant forall j :: 0 <= j < i && s[j] in last ==> (forall k :: 0 <= last[s[j]] < k < i ==> s[j] != s[k]);
    invariant forall j :: 0 <= j < i ==> s[j] in last;
    invariant forall k :: k in last ==> k in s[..i];
    invariant forall k :: k in last ==> 0 <= last[k] < i;
    invariant left <= i;
    invariant left >= 0;
    {
        if s[i] in last {
            left := max(left, last[s[i]] + 1);
        }
        last := last[ s[i] := i];
        maxL := max(maxL, i - left + 1);
        i := i + 1;
    }
    return maxL;
    /*
        last = dict()
        maxL = left = 0
        for i in range(len(s)):
            if s[i] in last:                
                left = max(left, last[s[i]] + 1)
            last[s[i]] = i
            maxL = max(maxL, i - left + 1)
            
        return maxL
    */
}