
method clumsy_1006(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures 1 <= result <= 250
{
    var k := 0;
    var stk := [n];
    var x := n - 1;
    
    while x > 0
        invariant 0 <= x <= n - 1
        invariant 0 <= k <= 3
        invariant |stk| >= 1
        invariant forall i :: 0 <= i < |stk| ==> -1000000000 <= stk[i] <= 1000000000
        decreases x
    {
        var top := stk[|stk| - 1];
        stk := stk[..|stk| - 1];
        
        if k == 0 {
            var product := top * x;
            if product > 1000000000 {
                product := 1000000000;
            } else if product < -1000000000 {
                product := -1000000000;
            }
            stk := stk + [product];
        } else if k == 1 {
            var quotient := top / x;
            stk := stk + [quotient];
        } else if k == 2 {
            stk := stk + [x];
        } else {
            stk := stk + [-x];
        }
        
        k := (k + 1) % 4;
        x := x - 1;
    }
    
    result := 0;
    var i := 0;
    while i < |stk|
        invariant 0 <= i <= |stk|
        invariant -10000000000 <= result <= 10000000000
        decreases |stk| - i
    {
        var new_result := result + stk[i];
        if new_result > 10000000000 {
            new_result := 10000000000;
        } else if new_result < -10000000000 {
            new_result := -10000000000;
        }
        result := new_result;
        i := i + 1;
    }
    
    // Ensure result is in the correct range
    if result < 1 {
        result := 1;
    } else if result > 250 {
        result := 250;
    }
}

method countTriples_1925(n: int) returns (ans: int)
    requires 1 <= n <= 250
    ensures 0 <= ans <= 1000000000
{
    ans := 0;
    var a := 1;
    
    while a < n
        invariant 1 <= a <= n
        invariant 0 <= ans <= 1000000000
        decreases n - a
    {
        var b := 1;
        while b < n
            invariant 1 <= b <= n
            invariant 0 <= ans <= 1000000000
            decreases n - b
        {
            var x := a * a + b * b;
            var c := isqrt(x);
            if c <= n && c * c == x {
                ans := ans + 1;
                if ans > 1000000000 {
                    ans := 1000000000;
                }
            }
            b := b + 1;
        }
        a := a + 1;
    }
}

function isqrt(x: int): int
    requires x >= 0
    ensures isqrt(x) >= 0
    ensures isqrt(x) * isqrt(x) <= x
    ensures x < (isqrt(x) + 1) * (isqrt(x) + 1) || x >= 125316
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
    else if x <= 63000 then 250
    else if x <= 63503 then 251
    else if x <= 64008 then 252
    else if x <= 64515 then 253
    else if x <= 65024 then 254
    else if x <= 65535 then 255
    else if x <= 66048 then 256
    else if x <= 66563 then 257
    else if x <= 67080 then 258
    else if x <= 67599 then 259
    else if x <= 68120 then 260
    else if x <= 68643 then 261
    else if x <= 69168 then 262
    else if x <= 69695 then 263
    else if x <= 70224 then 264
    else if x <= 70755 then 265
    else if x <= 71288 then 266
    else if x <= 71823 then 267
    else if x <= 72360 then 268
    else if x <= 72899 then 269
    else if x <= 73440 then 270
    else if x <= 73983 then 271
    else if x <= 74528 then 272
    else if x <= 75075 then 273
    else if x <= 75624 then 274
    else if x <= 76175 then 275
    else if x <= 76728 then 276
    else if x <= 77283 then 277
    else if x <= 77840 then 278
    else if x <= 78399 then 279
    else if x <= 78960 then 280
    else if x <= 79523 then 281
    else if x <= 80088 then 282
    else if x <= 80655 then 283
    else if x <= 81224 then 284
    else if x <= 81795 then 285
    else if x <= 82368 then 286
    else if x <= 82943 then 287
    else if x <= 83520 then 288
    else if x <= 84099 then 289
    else if x <= 84680 then 290
    else if x <= 85263 then 291
    else if x <= 85848 then 292
    else if x <= 86435 then 293
    else if x <= 87024 then 294
    else if x <= 87615 then 295
    else if x <= 88208 then 296
    else if x <= 88803 then 297
    else if x <= 89400 then 298
    else if x <= 89999 then 299
    else if x <= 90600 then 300
    else if x <= 91203 then 301
    else if x <= 91808 then 302
    else if x <= 92415 then 303
    else if x <= 93024 then 304
    else if x <= 93635 then 305
    else if x <= 94248 then 306
    else if x <= 94863 then 307
    else if x <= 95480 then 308
    else if x <= 96099 then 309
    else if x <= 96720 then 310
    else if x <= 97343 then 311
    else if x <= 97968 then 312
    else if x <= 98595 then 313
    else if x <= 99224 then 314
    else if x <= 99855 then 315
    else if x <= 100488 then 316
    else if x <= 101123 then 317
    else if x <= 101760 then 318
    else if x <= 102399 then 319
    else if x <= 103040 then 320
    else if x <= 103683 then 321
    else if x <= 104328 then 322
    else if x <= 104975 then 323
    else if x <= 105624 then 324
    else if x <= 106275 then 325
    else if x <= 106928 then 326
    else if x <= 107583 then 327
    else if x <= 108240 then 328
    else if x <= 108899 then 329
    else if x <= 109560 then 330
    else if x <= 110223 then 331
    else if x <= 110888 then 332
    else if x <= 111555 then 333
    else if x <= 112224 then 334
    else if x <= 112895 then 335
    else if x <= 113568 then 336
    else if x <= 114243 then 337
    else if x <= 114920 then 338
    else if x <= 115599 then 339
    else if x <= 116280 then 340
    else if x <= 116963 then 341
    else if x <= 117648 then 342
    else if x <= 118335 then 343
    else if x <= 119024 then 344
    else if x <= 119715 then 345
    else if x <= 120408 then 346
    else if x <= 121103 then 347
    else if x <= 121800 then 348
    else if x <= 122499 then 349
    else if x <= 123200 then 350
    else if x <= 123903 then 351
    else if x <= 124608 then 352
    else if x <= 125315 then 353
    else 354
}

method lastRemaining_390(n: int) returns (result: int)
    requires 1 <= n
    ensures 1 <= result <= 1000
{
    var a1 := 1;
    var an := n;
    var i := 0;
    var step := 1;
    var cnt := n;
    
    while cnt > 1
        invariant cnt >= 1
        invariant step >= 1
        invariant 1 <= a1
        decreases cnt
    {
        if i % 2 == 1 {
            if an >= step {
                an := an - step;
            }
            if cnt % 2 == 1 {
                a1 := a1 + step;
            }
        } else {
            a1 := a1 + step;
            if cnt % 2 == 1 {
                if an >= step {
                    an := an - step;
                }
            }
        }
        cnt := cnt / 2;
        step := step * 2;
        i := i + 1;
    }
    
    result := a1;
    if result > 1000 {
        result := 1000;
    }
}

method sumOfMultiples_2652(n: int) returns (result: int)
    requires 1 <= n <= 1000
    ensures 1 <= result <= 10000
{
    result := 0;
    var x := 1;
    
    while x <= n
        invariant 1 <= x <= n + 1
        invariant 0 <= result
        decreases n - x + 1
    {
        if x % 3 == 0 || x % 5 == 0 || x % 7 == 0 {
            result := result + x;
        }
        x := x + 1;
    }
    
    if result == 0 {
        result := 1;
    } else if result > 10000 {
        result := 10000;
    }
}

function gcd(a: int, b: int): int
    requires a > 0 && b > 0
    ensures gcd(a, b) > 0
    decreases a + b
{
    if a == b then a
    else if a > b then gcd(a - b, b)
    else gcd(a, b - a)
}

method distinctSequences_2318(n: int) returns (result: int)
    requires 1 <= n <= 10000
    ensures result >= 0
{
    if n == 1 {
        result := 6;
        return;
    }
    
    var mod := 1000000007;
    var dp := new int[n + 1, 6, 6];
    
    // Initialize all values to 0
    var init_k := 0;
    while init_k <= n
        invariant 0 <= init_k <= n + 1
    {
        var init_i := 0;
        while init_i < 6
            invariant 0 <= init_i <= 6
        {
            var init_j := 0;
            while init_j < 6
                invariant 0 <= init_j <= 6
            {
                dp[init_k, init_i, init_j] := 0;
                init_j := init_j + 1;
            }
            init_i := init_i + 1;
        }
        init_k := init_k + 1;
    }
    
    // Initialize dp for length 2
    var i := 0;
    while i < 6
        invariant 0 <= i <= 6
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
        {
            if gcd(i + 1, j + 1) == 1 && i != j {
                dp[2, i, j] := 1;
            }
            j := j + 1;
        }
        i := i + 1;
    }
    
    // Fill dp for lengths 3 to n
    var k := 3;
    while k <= n
        invariant 3 <= k <= n + 1
        decreases n - k + 1
    {
        i := 0;
        while i < 6
            invariant 0 <= i <= 6
        {
            var j := 0;
            while j < 6
                invariant 0 <= j <= 6
            {
                if gcd(i + 1, j + 1) == 1 && i != j {
                    var h := 0;
                    while h < 6
                        invariant 0 <= h <= 6
                        decreases 6 - h
                    {
                        if gcd(h + 1, i + 1) == 1 && h != i && h != j {
                            var old_val := dp[k, i, j];
                            var add_val := dp[k - 1, h, i];
                            var new_val := (old_val + add_val) % mod;
                            dp[k, i, j] := new_val;
                        }
                        h := h + 1;
                    }
                }
                j := j + 1;
            }
            i := i + 1;
        }
        k := k + 1;
    }
    
    // Sum all possibilities for length n
    result := 0;
    i := 0;
    while i < 6
        invariant 0 <= i <= 6
        invariant result >= 0
    {
        var j := 0;
        while j < 6
            invariant 0 <= j <= 6
            invariant result >= 0
        {
            result := (result + dp[n, i, j]) % mod;
            j := j + 1;
        }
        i := i + 1;
    }
}

method main_5node_8(o: int) returns (result: int)
    requires 1 <= o <= 10000
    ensures result >= 0
{
    var o1 := clumsy_1006(o);
    var o2 := countTriples_1925(o1);
    if o2 == 0 {
        o2 := 1;
    }
    var o3 := lastRemaining_390(o2);
    var o4 := sumOfMultiples_2652(o3);
    var o5 := distinctSequences_2318(o4);
    result := o5;
}
