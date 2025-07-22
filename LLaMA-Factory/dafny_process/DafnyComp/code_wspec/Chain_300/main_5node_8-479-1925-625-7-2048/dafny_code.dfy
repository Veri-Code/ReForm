
method largestPalindrome_479(n: int) returns (result: int)
    requires 1 <= n <= 8
    ensures 1 <= result <= 250
{
    var mx := power10(n) - 1;
    var a := mx;
    
    while a > mx / 10
        invariant mx / 10 < a <= mx || a == mx / 10
        invariant mx == power10(n) - 1
        decreases a
    {
        // Create palindrome by mirroring a
        var b := a;
        var x := a;
        while b > 0
            invariant b >= 0
            invariant x >= a
            decreases b
        {
            x := x * 10 + b % 10;
            b := b / 10;
        }
        
        // Check if x has a factor in valid range
        var t := mx;
        while t * t >= x && t > 0
            invariant t >= 0
            decreases t
        {
            if x % t == 0 {
                var res := x % 1337;
                if res == 0 { res := 1; }
                if res > 250 { res := 250; }
                return res;
            }
            t := t - 1;
        }
        a := a - 1;
    }
    return 9;
}

method countTriples_1925(n: int) returns (result: int)
    requires 1 <= n <= 250
    ensures 1 <= result <= 2147483648
{
    var ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant ans >= 0
        decreases n - a
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant ans >= 0
            decreases n - b
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
            }
            b := b + 1;
        }
        a := a + 1;
    }
    
    if ans == 0 { ans := 1; }
    if ans > 2147483648 { ans := 2147483648; }
    return ans;
}

method smallestFactorization_625(num: int) returns (result: int)
    requires 1 <= num <= 2147483648
    ensures -2147483648 <= result <= 2147483648
{
    if num < 2 {
        return num;
    }
    
    var ans := 0;
    var mul := 1;
    var remaining := num;
    var i := 9;
    
    while i > 1
        invariant 1 <= i <= 9
        invariant remaining >= 1
        invariant ans >= 0
        invariant mul >= 1
        decreases i
    {
        while remaining % i == 0
            invariant remaining >= 1
            invariant ans >= 0
            invariant mul >= 1
            decreases remaining
        {
            remaining := remaining / i;
            ans := mul * i + ans;
            mul := mul * 10;
            if mul > 214748364 { // Prevent overflow
                return 0;
            }
        }
        i := i - 1;
    }
    
    if remaining < 2 && ans <= 2147483647 {
        return ans;
    } else {
        return 0;
    }
}

method reverse_7(x: int) returns (result: int)
    requires -2147483648 <= x <= 2147483648
    ensures 0 <= result <= 1000000
{
    var ans := 0;
    var remaining := x;
    var mi := -2147483648;
    var mx := 2147483647;
    
    while remaining != 0
        invariant 0 <= ans <= 1000000
        decreases if remaining >= 0 then remaining else -remaining
    {
        if ans < mi / 10 + 1 || ans > mx / 10 {
            return 0;
        }
        
        var y := remaining % 10;
        if remaining < 0 && y > 0 {
            y := y - 10;
        }
        
        var newAns := ans * 10 + y;
        if newAns < 0 || newAns > 1000000 {
            return 0;
        }
        ans := newAns;
        remaining := (remaining - y) / 10;
    }
    
    return ans;
}

method nextBeautifulNumber_2048(n: int) returns (result: int)
    requires 0 <= n <= 1000000
    ensures result >= 1
{
    var x := n + 1;
    
    while x <= 1224444  // Upper bound to ensure termination
        invariant x >= n + 1
        decreases 1224444 - x
    {
        if isBeautiful(x) {
            return x;
        }
        x := x + 1;
    }
    
    return 1224444; // Fallback beautiful number
}

function isBeautiful(x: int): bool
    requires x >= 0
{
    var counts := getDigitCountsFunction(x);
    forall i :: 0 <= i <= 9 ==> (counts[i] == 0 || counts[i] == i)
}

function getDigitCountsFunction(x: int): seq<int>
    requires x >= 0
    ensures |getDigitCountsFunction(x)| == 10
    ensures forall i :: 0 <= i < 10 ==> getDigitCountsFunction(x)[i] >= 0
{
    var counts := seq(10, i => 0);
    getDigitCountsHelper(x, counts)
}

function getDigitCountsHelper(x: int, counts: seq<int>): seq<int>
    requires x >= 0
    requires |counts| == 10
    requires forall i :: 0 <= i < 10 ==> counts[i] >= 0
    ensures |getDigitCountsHelper(x, counts)| == 10
    ensures forall i :: 0 <= i < 10 ==> getDigitCountsHelper(x, counts)[i] >= 0
    decreases x
{
    if x == 0 then counts
    else
        var digit := x % 10;
        var newCounts := if 0 <= digit <= 9 then counts[digit := counts[digit] + 1] else counts;
        getDigitCountsHelper(x / 10, newCounts)
}

function power10(n: int): int
    requires 0 <= n <= 8
    ensures power10(n) >= 1
{
    if n == 0 then 1
    else if n == 1 then 10
    else if n == 2 then 100
    else if n == 3 then 1000
    else if n == 4 then 10000
    else if n == 5 then 100000
    else if n == 6 then 1000000
    else if n == 7 then 10000000
    else 100000000
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x
    ensures x < 63000 ==> (isqrt(x) + 1) * (isqrt(x) + 1) > x
{
    if x == 0 then 0
    else if x <= 3 then 1
    else if x <= 8 then 2
    else if x <= 15 then 3
    else if x <= 24 then 4
    else if x <= 35 then 5
    else if x <= 48 then 6
    else if x <= 63 then 7
    else if x <= 80 then 8
    else if x <= 99 then 9
    else if x <= 120 then 10
    else if x <= 143 then 11
    else if x <= 168 then 12
    else if x <= 195 then 13
    else if x <= 224 then 14
    else if x <= 255 then 15
    else if x <= 288 then 16
    else if x <= 323 then 17
    else if x <= 360 then 18
    else if x <= 399 then 19
    else if x <= 440 then 20
    else if x <= 483 then 21
    else if x <= 528 then 22
    else if x <= 575 then 23
    else if x <= 624 then 24
    else if x <= 675 then 25
    else if x <= 728 then 26
    else if x <= 783 then 27
    else if x <= 840 then 28
    else if x <= 899 then 29
    else if x <= 960 then 30
    else if x <= 1023 then 31
    else if x <= 1088 then 32
    else if x <= 1155 then 33
    else if x <= 1224 then 34
    else if x <= 1295 then 35
    else if x <= 1368 then 36
    else if x <= 1443 then 37
    else if x <= 1520 then 38
    else if x <= 1599 then 39
    else if x <= 1680 then 40
    else if x <= 1763 then 41
    else if x <= 1848 then 42
    else if x <= 1935 then 43
    else if x <= 2024 then 44
    else if x <= 2115 then 45
    else if x <= 2208 then 46
    else if x <= 2303 then 47
    else if x <= 2400 then 48
    else if x <= 2499 then 49
    else if x <= 2600 then 50
    else if x <= 2703 then 51
    else if x <= 2808 then 52
    else if x <= 2915 then 53
    else if x <= 3024 then 54
    else if x <= 3135 then 55
    else if x <= 3248 then 56
    else if x <= 3363 then 57
    else if x <= 3480 then 58
    else if x <= 3599 then 59
    else if x <= 3720 then 60
    else if x <= 3843 then 61
    else if x <= 3968 then 62
    else if x <= 4095 then 63
    else if x <= 4224 then 64
    else if x <= 4355 then 65
    else if x <= 4488 then 66
    else if x <= 4623 then 67
    else if x <= 4760 then 68
    else if x <= 4899 then 69
    else if x <= 5040 then 70
    else if x <= 5183 then 71
    else if x <= 5328 then 72
    else if x <= 5475 then 73
    else if x <= 5624 then 74
    else if x <= 5775 then 75
    else if x <= 5928 then 76
    else if x <= 6083 then 77
    else if x <= 6240 then 78
    else if x <= 6399 then 79
    else if x <= 6560 then 80
    else if x <= 6723 then 81
    else if x <= 6888 then 82
    else if x <= 7055 then 83
    else if x <= 7224 then 84
    else if x <= 7395 then 85
    else if x <= 7568 then 86
    else if x <= 7743 then 87
    else if x <= 7920 then 88
    else if x <= 8099 then 89
    else if x <= 8280 then 90
    else if x <= 8463 then 91
    else if x <= 8648 then 92
    else if x <= 8835 then 93
    else if x <= 9024 then 94
    else if x <= 9215 then 95
    else if x <= 9408 then 96
    else if x <= 9603 then 97
    else if x <= 9800 then 98
    else if x <= 9999 then 99
    else if x <= 10200 then 100
    else if x <= 10403 then 101
    else if x <= 10608 then 102
    else if x <= 10815 then 103
    else if x <= 11024 then 104
    else if x <= 11235 then 105
    else if x <= 11448 then 106
    else if x <= 11663 then 107
    else if x <= 11880 then 108
    else if x <= 12099 then 109
    else if x <= 12320 then 110
    else if x <= 12543 then 111
    else if x <= 12768 then 112
    else if x <= 12995 then 113
    else if x <= 13224 then 114
    else if x <= 13455 then 115
    else if x <= 13688 then 116
    else if x <= 13923 then 117
    else if x <= 14160 then 118
    else if x <= 14399 then 119
    else if x <= 14640 then 120
    else if x <= 14883 then 121
    else if x <= 15128 then 122
    else if x <= 15375 then 123
    else if x <= 15624 then 124
    else if x <= 15875 then 125
    else if x <= 16128 then 126
    else if x <= 16383 then 127
    else if x <= 16640 then 128
    else if x <= 16899 then 129
    else if x <= 17160 then 130
    else if x <= 17423 then 131
    else if x <= 17688 then 132
    else if x <= 17955 then 133
    else if x <= 18224 then 134
    else if x <= 18495 then 135
    else if x <= 18768 then 136
    else if x <= 19043 then 137
    else if x <= 19320 then 138
    else if x <= 19599 then 139
    else if x <= 19880 then 140
    else if x <= 20163 then 141
    else if x <= 20448 then 142
    else if x <= 20735 then 143
    else if x <= 21024 then 144
    else if x <= 21315 then 145
    else if x <= 21608 then 146
    else if x <= 21903 then 147
    else if x <= 22200 then 148
    else if x <= 22499 then 149
    else if x <= 22800 then 150
    else if x <= 23103 then 151
    else if x <= 23408 then 152
    else if x <= 23715 then 153
    else if x <= 24024 then 154
    else if x <= 24335 then 155
    else if x <= 24648 then 156
    else if x <= 24963 then 157
    else if x <= 25280 then 158
    else if x <= 25599 then 159
    else if x <= 25920 then 160
    else if x <= 26243 then 161
    else if x <= 26568 then 162
    else if x <= 26895 then 163
    else if x <= 27224 then 164
    else if x <= 27555 then 165
    else if x <= 27888 then 166
    else if x <= 28223 then 167
    else if x <= 28560 then 168
    else if x <= 28899 then 169
    else if x <= 29240 then 170
    else if x <= 29583 then 171
    else if x <= 29928 then 172
    else if x <= 30275 then 173
    else if x <= 30624 then 174
    else if x <= 30975 then 175
    else if x <= 31328 then 176
    else if x <= 31683 then 177
    else if x <= 32040 then 178
    else if x <= 32399 then 179
    else if x <= 32760 then 180
    else if x <= 33123 then 181
    else if x <= 33488 then 182
    else if x <= 33855 then 183
    else if x <= 34224 then 184
    else if x <= 34595 then 185
    else if x <= 34968 then 186
    else if x <= 35343 then 187
    else if x <= 35720 then 188
    else if x <= 36099 then 189
    else if x <= 36480 then 190
    else if x <= 36863 then 191
    else if x <= 37248 then 192
    else if x <= 37635 then 193
    else if x <= 38024 then 194
    else if x <= 38415 then 195
    else if x <= 38808 then 196
    else if x <= 39203 then 197
    else if x <= 39600 then 198
    else if x <= 39999 then 199
    else if x <= 40400 then 200
    else if x <= 40803 then 201
    else if x <= 41208 then 202
    else if x <= 41615 then 203
    else if x <= 42024 then 204
    else if x <= 42435 then 205
    else if x <= 42848 then 206
    else if x <= 43263 then 207
    else if x <= 43680 then 208
    else if x <= 44099 then 209
    else if x <= 44520 then 210
    else if x <= 44943 then 211
    else if x <= 45368 then 212
    else if x <= 45795 then 213
    else if x <= 46224 then 214
    else if x <= 46655 then 215
    else if x <= 47088 then 216
    else if x <= 47523 then 217
    else if x <= 47960 then 218
    else if x <= 48399 then 219
    else if x <= 48840 then 220
    else if x <= 49283 then 221
    else if x <= 49728 then 222
    else if x <= 50175 then 223
    else if x <= 50624 then 224
    else if x <= 51075 then 225
    else if x <= 51528 then 226
    else if x <= 51983 then 227
    else if x <= 52440 then 228
    else if x <= 52899 then 229
    else if x <= 53360 then 230
    else if x <= 53823 then 231
    else if x <= 54288 then 232
    else if x <= 54755 then 233
    else if x <= 55224 then 234
    else if x <= 55695 then 235
    else if x <= 56168 then 236
    else if x <= 56643 then 237
    else if x <= 57120 then 238
    else if x <= 57599 then 239
    else if x <= 58080 then 240
    else if x <= 58563 then 241
    else if x <= 59048 then 242
    else if x <= 59535 then 243
    else if x <= 60024 then 244
    else if x <= 60515 then 245
    else if x <= 61008 then 246
    else if x <= 61503 then 247
    else if x <= 62000 then 248
    else if x <= 62499 then 249
    else if x <= 62999 then 250
    else 250
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 8
    ensures result >= 1
{
    var o1 := largestPalindrome_479(o);
    var o2 := countTriples_1925(o1);
    var o3 := smallestFactorization_625(o2);
    var o4 := reverse_7(o3);
    var o5 := nextBeautifulNumber_2048(o4);
    result := o5;
}
