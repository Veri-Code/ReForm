import re
import os
import json
from difflib import SequenceMatcher

def normalize_spec(spec: str) -> str:
    """Normalize a specification by removing whitespace and comments."""
    # Remove comments
    spec = re.sub(r'//.*$', '', spec, flags=re.MULTILINE)
    # Normalize whitespace
    spec = re.sub(r'\s+', ' ', spec)
    return spec.strip()

def extract_clauses(block: str, keyword: str) -> list[str]:
    """
    From a block of Dafny code, return every clause that begins
    with `keyword` (e.g. 'requires' or 'ensures'), capturing all
    lines up to (but not including) the next STOP_KEYWORD line.
    """
    lines = block.splitlines()
    clauses = []
    i = 0
    stop_kw = ["requires", "ensures", "decreases", "reads", "modifies"]

    while i < len(lines):
        line = lines[i].lstrip()
        if line.strip().startswith("{"):
            break
        if line.startswith(keyword):
            # Start collecting this clause
            collected = [ line[len(keyword):].strip() ]  # drop the leading keyword
            i += 1
            # Gather lines until the next STOP_KEYWORD or end of block
            while i < len(lines):
                nxt = lines[i].lstrip()
                # if next line begins with any stop keyword, break
                if any(nxt.startswith(kw) for kw in stop_kw) or nxt.strip().endswith(";"):
                    break
                # otherwise, include this line
                collected.append(nxt)
                i += 1
            # join and normalize whitespace
            clause_text = " ".join(p for p in collected if p).strip()
            if clause_text.endswith("{"):
                clause_text = clause_text[:-1]  # Remove the last character
            clauses.append(clause_text)
        else:
            i += 1
    return clauses or []


def extract_specs(dafny_code: str):
    """
    Returns a dict:
      { method_name: {"requires": [ ... ], "ensures": [ ... ]} }
    """
    
    def find_method_signature_end(code, start_pos):
        """Find the end of a method signature by looking for the method body opening brace.
        
        The method body opening brace should be at the beginning of a line (possibly with whitespace),
        distinguishing it from braces within specifications like ensures result.Keys >= {"dummy"}.
        If we encounter a semicolon, we return the position after the last brace we saw.
        """
        pos = start_pos
        last_brace_pos = -1
        next_method_pattern = re.compile(r'^\s*(?:method|function|constructor|lemma|class|predicate|two_state|ghost)\s+\w+')
        match = next_method_pattern.match(code[pos:])
        if match:
            end_pos = pos + match.start()
        else:
            end_pos = len(code)
        
        while pos < end_pos:
            if code[pos] == '{':
                # Record this brace position
                last_brace_pos = pos
                
                # Check if this brace is at the start of a line (method body opening)
                # Look backwards to see if there's only whitespace before this brace on the line
                line_start = code.rfind('\n', 0, pos) + 1
                before_brace = code[line_start:pos].strip()
                
                if before_brace == '':  # Only whitespace before the brace on this line
                    return pos + 1  # Return position after the opening brace
                    
            elif code[pos] == ';':
                # Found semicolon, return position after the last brace we saw
                if last_brace_pos != -1:
                    return last_brace_pos + 1
                else:
                    # No brace found before semicolon, this might be a method declaration
                    return pos + 1
                    
            pos += 1
            
        return -1  # Not found
    
    specs = {}
    
    # Find method/function signatures using a simpler initial pattern
    sig_re = re.compile(
        r'((?:ghost\s+)?(?:method|function)\s+(\w+))',
        re.DOTALL | re.MULTILINE
    )
    
    parts = []
    for match in sig_re.finditer(dafny_code):
        name = match.group(2)
        start_pos = match.start()
        end_pos = find_method_signature_end(dafny_code, match.end()-2)
        
        if end_pos != -1:
            parts.append({
                'match': match,
                'name': name,
                'start': start_pos,
                'end': end_pos
            })
    
    for part in parts:
        name = part['name']
        start = part['start']
        end = part['end']
        # Extract the block from start to just before the opening brace
        block = dafny_code[start:end-1]

        # Match requires/ensures up to the next keyword (no semicolons needed)
        reqs = extract_clauses(block, 'requires')
        enss = extract_clauses(block, 'ensures')

        specs[name] = {"requires": reqs, "ensures": enss}

    return specs

def is_similar_spec(spec1: str, spec2: str, threshold: float = 0.85) -> bool:
    """Check if two specs are similar using sequence matcher."""
    # Normalize both specs
    spec1 = normalize_spec(spec1)
    spec2 = normalize_spec(spec2)
    
    # Use sequence matcher to compare
    matcher = SequenceMatcher(None, spec1, spec2)
    return matcher.ratio() >= threshold

def analyze_spec_coverage(gt_code: str, code: str, output_file: str):
    """
    Analyze spec coverage between ground truth and code.
    Saves uncovered specs to output file.
    
    Args:
        gt_code: Ground truth Dafny code
        code: Code to analyze
        output_file: Path to save results
    
    Returns:
        tuple: (requires_coverage, ensures_coverage)
    """
    # Extract specs from both codes
    gt_specs = extract_specs(gt_code)
    code_specs = extract_specs(code)
    
    results = {}
    
    total_requires = 0
    total_ensures = 0
    covered_requires = 0
    covered_ensures = 0
    
    # For each method in ground truth
    for method, gt_spec in gt_specs.items():
        method_results = {
            "uncovered_requires": [],
            "uncovered_ensures": [],
            "covered_ensures": []
        }
        
        # Count total specs
        # print("DEBUG: ", method, gt_spec["requires"], gt_spec["ensures"])
        total_requires += len(gt_spec["requires"])
        total_ensures += len(gt_spec["ensures"])
        
        # If method exists in code
        if method in code_specs:
            code_spec = code_specs[method]
            
            # Check requires coverage
            for gt_req in gt_spec["requires"]:
                covered = False
                for code_req in code_spec["requires"]:
                    if is_similar_spec(gt_req, code_req):
                        covered = True
                        covered_requires += 1
                        break
                if not covered:
                    method_results["uncovered_requires"].append(gt_req)
            
            # Check ensures coverage
            for gt_ens in gt_spec["ensures"]:
                covered = False
                for code_ens in code_spec["ensures"]:
                    if is_similar_spec(gt_ens, code_ens):
                        covered = True
                        covered_ensures += 1
                        method_results["covered_ensures"].append(code_ens)
                        break
                if not covered:
                    method_results["uncovered_ensures"].append(gt_ens)
        else:
            # Method/constructor not found - all specs uncovered
            method_results["uncovered_requires"].extend(gt_spec["requires"])
            method_results["uncovered_ensures"].extend(gt_spec["ensures"])
        
        # Only add method/constructor to results if it has uncovered specs
        if method_results["uncovered_requires"] or method_results["uncovered_ensures"]:
            results[method] = method_results
    
    # Calculate coverage ratios
    requires_coverage = covered_requires / total_requires if total_requires > 0 else 0
    ensures_coverage = covered_ensures / total_ensures if total_ensures > 0 else 0
    
    # Add coverage stats to results
    results["coverage_stats"] = {
        "requires_coverage": requires_coverage,
        "ensures_coverage": ensures_coverage,
        "total_requires": total_requires,
        "total_ensures": total_ensures,
        "covered_requires": covered_requires,
        "covered_ensures": covered_ensures
    }
    
    # Save results to file
    os.makedirs(os.path.dirname(output_file), exist_ok=True)
    with open(output_file, 'w') as f:
        json.dump(results, f, indent=2)
    
    return requires_coverage, ensures_coverage 