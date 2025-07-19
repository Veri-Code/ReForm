#!/usr/bin/env python3
import os
import sys
from spec_coverage import analyze_spec_coverage

def main(gt_code, code):
    """
    Analyze spec coverage between ground truth and code files.
    Usage: analyze_coverage.py <ground_truth_file> <code_file> <output_dir>
    """
        
    # Create output filename based on input file
    output_file = "/nas/shared/sys2/liyizhi/test_tinyzero3/coverage.json"
    
    # Analyze coverage
    requires_coverage, ensures_coverage = analyze_spec_coverage(gt_code, code, output_file)
    
    # Print summary
    print(f"Requires Coverage: {requires_coverage:.2%}")
    print(f"Ensures Coverage: {ensures_coverage:.2%}")
    print(f"\nDetailed results saved to: {output_file}")

if __name__ == "__main__":
    gt_code = """
    ```dafny
class HydroInstance {
  var matrices: map<int, map<int, map<int, map<int, real>>>>
  var initialInflows: seq<seq<real>>
  var noiseMatrix: array3<real>
  constructor(ar: map<int, map<int, map<int, map<int, real>>>>,
              inflows: seq<seq<real>>,
              noise: array3<real>)
    requires |ar| > 0 && |inflows| > 0
    requires forall i :: 0 <= i < |ar| ==> i in ar.Keys
    requires forall i, j :: 0 <= i < |ar| && j in ar[i] ==> j in ar[i].Keys
    requires forall i, j, k :: 0 <= i < |ar| && j in ar[i] && k in ar[i][j] ==> k in ar[i][j].Keys
    requires noise.Length0 > 0 && noise.Length1 > 0 && noise.Length2 > 0
    ensures matrices == ar
    ensures initialInflows == inflows
    ensures noiseMatrix == noise
  {
    matrices := ar;
    initialInflows := inflows;
    noiseMatrix := noise;
  }
}
method RandomReal(min: real, max: real) returns (r: real)
  requires min < max
  ensures min <= r <= max
{
  
  
  r := min + (max - min) / 2.0;
}
function SinApprox(x: real): real
{
  
  
  x - (x * x * x) / 6.0
}
method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
  returns (matrices: map<int, map<int, map<int, real>>>)
  requires numReservoirs > 0 && upStreamDep >= 0 && lag > 0
  requires t >= 0 && season > 0
  ensures |matrices| <= lag + 1
  ensures forall i :: 0 <= i < |matrices| ==> i in matrices.Keys
{
  matrices := map[];
  var l := 1;
  
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
          if t < season {
            
            value := 0.5 + 0.5 * SinApprox(t as real);
          } else {
            value := 0.5;
          }
          upstreamMap := upstreamMap[i-j := value];
        }
        j := j + 1;
      }
      if |upstreamMap| > 0 {
        reservoirMap := reservoirMap[i := upstreamMap];
      }
      i := i + 1;
    }
    matrices := matrices[l := reservoirMap];
    l := l + 1;
  }
}
```"""
    code = """
    ```dafny
class HydroInstance {
  var matrices: map<int, map<int, map<int, map<int, real>>>>
  var initialInflows: seq<seq<real>>
  var noiseMatrix: array3<real>
  constructor(ar: map<int, map<int, map<int, map<int, real>>>>,
              inflows: seq<seq<real>>,
              noise: array3<real>)
    requires |ar| > 0 && |inflows| > 0
    requires forall i :: 0 <= i < |ar| ==> i in ar.Keys
    requires forall i, j :: 0 <= i < |ar| && j in ar[i] ==> j in ar[i].Keys
    requires forall i, j, k :: 0 <= i < |ar| && j in ar[i] && k in ar[i][j] ==> k in ar[i][j].Keys
    requires noise.Length0 > 0 && noise.Length1 > 0 && noise.Length2 > 0
    ensures matrices == ar
    ensures noiseMatrix == noise
  {
    matrices := ar;
    initialInflows := inflows;
    noiseMatrix := noise;
  }
}
method RandomReal(min: real, max: real) returns (r: real)
  requires min < max
  ensures min <= r <= max
{
  
  
  r := min + (max - min) / 2.0;
}
function SinApprox(x: real): real
{
  
  
  x - (x * x * x) / 6.0
}
method GenerateARMatrices(numReservoirs: int, upStreamDep: int, lag: int, t: int, season: int) 
  returns (matrices: map<int, map<int, map<int, real>>>)
  requires numReservoirs > 0 && upStreamDep >= 0 && lag > 0
  ensures forall i :: 0 <= i < |matrices|  ==> 
  i in matrices.Keys
{
  matrices := map[];
  var l := 1;
  
  while l <= lag
    invariant 1 <= l <= lag + 1
    invariant forall i :: 0 <= i < l ==> i in matrices.Keys
  {
    var reservoirMap := map[];
    var i := 0;
    while i < numReservoirs
      invariant 0 <= i <= numReservoirs
      invariant forall j :: 0 <= j < i ==> j in reservoirMap.Keys
      invariant forall j, k :: 0 <= j < i && k in reservoirMap[j] ==> k in reservoirMap[j].Keys
    {
      var upstreamMap := map[];
      var j := 0;
      while j <= upStreamDep
        invariant 0 <= j <= upStreamDep + 1
        invariant forall k :: 0 <= k < j ==> k in upstreamMap.Keys
        invariant forall k, l :: 0 <= k < j && l in upstreamMap[k] ==> l in upstreamMap[k].Keys
      {
        if i - j >= 0 {
          var value: real;
          if t < season {
            
            value := 0.5 + 0.5 * SinApprox(t as real);
          } else {
            value := 0.5;
          }
          upstreamMap := upstreamMap[i-j := value];
        }
        j := j + 1;
      }
      if |upstreamMap| > 0 {
        reservoirMap := reservoirMap[i := upstreamMap];
      }
      i := i + 1;
    }
    matrices := matrices[l := reservoirMap];
    l := l + 1;
  }
}
```"""
    main(gt_code,code) 