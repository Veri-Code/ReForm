import json
import time
from pathlib import Path
import os
import sys
from collections import defaultdict
import multiprocessing
import concurrent.futures
from functools import lru_cache
import argparse

import xxhash
import difflib
from tqdm import tqdm

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from src.utils import *

@lru_cache(maxsize=10000)
def is_similar(str1, str2, threshold=0.9):
    """Check if two strings are similar"""
    len1, len2 = len(str1), len(str2)
    if len1 == 0 or len2 == 0:
        return False
    
    if min(len1, len2) / max(len1, len2) < threshold * 0.5:
        return False
        
    if len1 < len2 and str1 in str2:
        return True
    if len2 < len1 and str2 in str1:
        return True
        
    ratio = difflib.SequenceMatcher(None, str1, str2).ratio()
    return ratio >= threshold

class MinHashLSH:
    """Improved MinHash LSH implementation with memory efficiency"""
    
    def __init__(self, num_perm=64, threshold=0.9, chunks=10):
        self.num_perm = num_perm
        self.threshold = threshold
        self.seed = 42
        self.chunks = chunks
        self.chunk_size = self.num_perm // self.chunks
        self.hash_ranges = [(i * self.chunk_size, (i + 1) * self.chunk_size) for i in range(self.chunks)]
        self.tables = [defaultdict(list) for _ in range(self.chunks)]
        self.items = {}
        
    def _create_signature(self, text):
        """Create MinHash signature with optimized shingle creation"""
        if not text or len(text) < 4:
            return [float('inf')] * self.num_perm
        
        n = 3  
        shingles = set()
        
        for i in range(len(text) - n + 1):
            shingle = text[i:i+n]
            shingles.add(shingle)
        
        if len(shingles) > 500:
            shingles = set(list(shingles)[:500])
        
        signature = [float('inf')] * self.num_perm
        
        for i in range(0, self.num_perm, 8):
            batch_size = min(8, self.num_perm - i)
            min_hashes = [float('inf')] * batch_size
            
            for shingle in shingles:
                base_hash = xxhash.xxh64(shingle, seed=self.seed).intdigest()
                
                for j in range(batch_size):
                    h = xxhash.xxh64(shingle + str(j), seed=base_hash).intdigest()
                    min_hashes[j] = min(min_hashes[j], h)
            
            for j in range(batch_size):
                signature[i+j] = min_hashes[j]
            
        return signature
        
    def add(self, key, text):
        """Add an item to the index with memory optimization"""
        sig = self._create_signature(text)
        
        text_hash = xxhash.xxh64(text).hexdigest()
        self.items[key] = (text_hash, sig, text)
        
        num_tables_to_use = max(1, min(3, self.chunks // 3))
        for i in range(num_tables_to_use):
            start, end = self.hash_ranges[i]
            bucket_key = tuple(sig[start:end])
            self.tables[i][bucket_key].append(key)
    
    def _signature_similarity(self, sig1, sig2):
        """Estimate Jaccard similarity from MinHash signatures"""
        matches = 0
        for i in range(self.num_perm):
            if sig1[i] == sig2[i]:
                matches += 1
        return matches / self.num_perm
    
    def contains_similar(self, text):
        """Check if index contains any text similar to the given one - with early stopping"""
        sig = self._create_signature(text)
        text_hash = xxhash.xxh64(text).hexdigest()
        
        candidates = set()
        num_tables_to_query = max(1, min(3, self.chunks // 3))
        
        for i in range(num_tables_to_query):
            start, end = self.hash_ranges[i]
            bucket_key = tuple(sig[start:end])
            curr_candidates = self.tables[i][bucket_key]
            if curr_candidates:
                candidates.update(curr_candidates)
                if len(candidates) > 20:
                    break
        
        if len(candidates) > 50:
            candidates = list(candidates)[:50]
            
        for key in candidates:
            stored_hash, stored_sig, stored_text = self.items[key]
            
            if text_hash == stored_hash:
                return True
                
            if self._signature_similarity(sig, stored_sig) >= self.threshold * 0.7:
                if is_similar(text, stored_text, self.threshold):
                    return True
        
        return False
    
    def deduplicate(self, texts):
        """Deduplicate a list of texts efficiently with progress reporting"""
        result = []
        total = len(texts)
        
        for i, text in enumerate(texts):
            if not self.contains_similar(text):
                self.add(len(self.items), text)
                result.append(text)
            
            if i % 100 == 0 or i == total - 1:
                progress = (i + 1) / total * 100
                print(f"\rDeduplicating with LSH: {progress:.1f}% ({i+1}/{total})", end="")
        
        print() 
        return result

def process_chunk_with_lsh(chunk, chunk_id):
    """Process a chunk of entries using LSH with chunk ID for progress tracking"""
    try:
        processed_chunk = []
        for text in chunk:
            if len(text) > 10000:
                text = text[:10000]
            processed_chunk.append(text)
        
        processed_chunk.sort(key=len)
        
        lsh = MinHashLSH(num_perm=32)  
        result = lsh.deduplicate(processed_chunk)
        return result, chunk_id
    except Exception as e:
        print(f"Error in chunk {chunk_id}: {e}")
        return [], chunk_id

def deduplicate_similar_optimized(list1, list2, threshold=0.9, workers=None):
    """
    Optimized parallel deduplication with improved memory management and load balancing
    
    Args:
        list1: First list of strings
        list2: Second list of strings
        threshold: Similarity threshold
        workers: Number of parallel workers
    
    Returns:
        Deduplicated list of strings
    """
    if workers is None:
        workers = min(4, max(2, os.cpu_count() // 2))
        
    print(f"Optimized deduplication for lists of sizes {len(list1)} and {len(list2)} using {workers} workers")
    
    list1 = [text for text in list1 if len(text) < 50000]
    list2 = [text for text in list2 if len(text) < 50000]
    
    list1.sort(key=len)
    list2.sort(key=len)
    
    combined = list1 + list2
    
    if len(combined) <= 1000:
        print("Small dataset, using direct LSH deduplication")
        lsh = MinHashLSH(threshold=threshold)
        return lsh.deduplicate(combined)
    
    total_size = len(combined)
    
    chunks = []
    chunk_size = max(50, min(150, total_size // (workers * 4)))  
    
    for i in range(0, total_size, chunk_size):
        end = min(i + chunk_size, total_size)
        chunks.append(combined[i:end])
    
    print(f"Split data into {len(chunks)} chunks for balanced processing")
    
    max_chunks_per_batch = max(1, min(workers, len(chunks)))
    
    all_deduplicated = []
    
    for batch_start in range(0, len(chunks), max_chunks_per_batch):
        batch_end = min(batch_start + max_chunks_per_batch, len(chunks))
        current_chunks = chunks[batch_start:batch_end]
        print(f"Processing batch {batch_start//max_chunks_per_batch + 1}: chunks {batch_start+1}-{batch_end}")
        
        with concurrent.futures.ProcessPoolExecutor(max_workers=min(workers, len(current_chunks))) as executor:
            futures = {}
            for i, chunk in enumerate(current_chunks):
                future = executor.submit(process_chunk_with_lsh, chunk, batch_start + i)
                futures[future] = batch_start + i
            
            batch_results = []
            
            timeout = 180 
            start_time = time.time()
            remaining_chunks = set(range(batch_start, batch_end))
            
            while futures and time.time() - start_time < timeout:
                done, not_done = concurrent.futures.wait(
                    list(futures.keys()), timeout=5.0, 
                    return_when=concurrent.futures.FIRST_COMPLETED
                )
                
                for future in done:
                    try:
                        chunk_id = futures[future]
                        result, _ = future.result(timeout=1.0)
                        batch_results.extend(result)
                        remaining_chunks.discard(chunk_id)
                        print(f"  - Completed chunk {chunk_id+1}, found {len(result)} unique items")
                        futures.pop(future)
                    except concurrent.futures.TimeoutError:
                        print(f"  - Timeout while retrieving results for chunk")
                        futures.pop(future)
                    except Exception as e:
                        print(f"  - Error processing chunk: {e}")
                        futures.pop(future)
                
                if futures:
                    elapsed = time.time() - start_time
                    print(f"  - Processing for {elapsed:.1f}s, {len(remaining_chunks)} chunks remaining")
            
            if futures:
                print(f"  - Batch processing timeout after {timeout}s. Cancelling {len(futures)} remaining tasks.")
                for future in futures:
                    future.cancel()
        
        if batch_end < len(chunks):
            print("Pausing between batches to free resources...")
            time.sleep(2)
        
        all_deduplicated.extend(batch_results)
        print(f"Processed batch {batch_start//max_chunks_per_batch + 1}, current unique items: {len(all_deduplicated)}")
    
    print(f"Final merging: {len(all_deduplicated)} items")
    
    lsh = MinHashLSH(threshold=threshold, num_perm=64)
    final_result = []
    
    batch_size = 200  
    for i in range(0, len(all_deduplicated), batch_size):
        end = min(i + batch_size, len(all_deduplicated))
        chunk = all_deduplicated[i:end]
        
        print(f"Final deduplication batch {i//batch_size + 1}/{(len(all_deduplicated)+batch_size-1)//batch_size}")
        for text in chunk:
            if not lsh.contains_similar(text):
                lsh.add(len(lsh.items), text)
                final_result.append(text)
        
        print(f"  - Progress: {min(end, len(all_deduplicated))}/{len(all_deduplicated)} items, {len(final_result)} unique")
    
    print(f"Final result: {len(final_result)} unique items")
    return final_result

def process_data(args):
    """Process and deduplicate datasets using advanced methods with command line arguments"""
    output_dir = Path(args.output_dir)
    output_dir.mkdir(exist_ok=True)
    
    start_total = time.time()
    
    print("=== Loading ===")
    print("Loading source1 data...")
    with open(args.source1_path, 'r') as f:
        source1 = json.load(f)
    
    print("Loading source2 data...")
    with open(args.source2_path, 'r') as f:
        source2 = json.load(f)
    
    print("\n=== Preprocessing ===")
    print("Preprocessing source1 data...")
    source1_origin = []
    for item in tqdm(source1, desc="Processing source1"):
        text = depend_remove(comment_remove(item['dafny']))
        if len(text) > 50000:  
            text = text[:50000]
        source1_origin.append(text)
    
    print("Preprocessing source2 data...")
    source2_origin = []
    for item in tqdm(source2, desc="Processing source2"):
        text = depend_remove(comment_remove(extract_dafny_code(item['output'])))
        if len(text) > 50000:  
            text = text[:50000]
        source2_origin.append(text)
    
    print(f"Original data sizes: source1={len(source1_origin)}, source2={len(source2_origin)}")
    
    try:
        print("\n=== Deduping ===")
        start_time = time.time()
        optimized_result = deduplicate_similar_optimized(
            source1_origin, 
            source2_origin, 
            threshold=args.threshold,
            workers=args.workers
        )
        optimized_time = time.time() - start_time
        
        total_time = time.time() - start_total
        print("\n=== Statistics ===")
        print(f"Total: {len(source1_origin) + len(source2_origin)}")
        print(f"Have dedupped: {len(optimized_result)} records, consuming {optimized_time:.2f} s")
        print(f"Total processing time: {total_time:.2f} s")
        
        optimized_dict_lst = []
        for item in optimized_result:
            optimized_dict_lst.append({
                'dafny': item,
            })

        if output_dir is not None:
            os.makedirs(output_dir, exist_ok=True)
        output_file = output_dir / 'deduped_optimized.json'
        with open(output_file, 'w') as f:
            json.dump(optimized_dict_lst, f)
        
        print(f"\nSaved to {output_file}")
    except KeyboardInterrupt:
        print("\nInterrupted.")
    except Exception as e:
        print(f"\nError: {e}")
    finally:
        print("Done with resource released")

def parse_args():
    """Parse command line arguments"""
    parser = argparse.ArgumentParser(
        description='Advanced deduplication for Dafny code datasets',
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    # Which field to use is needed to be specified, line 312
    parser.add_argument(
        '--source1-path',
        type=str,
        required=True,
        help='Path to the source1 dataset JSON file'
    )
    # Which field to use is needed to be specified, line 320
    parser.add_argument(
        '--source2-path',
        type=str,
        required=True,
        help='Path to the source2 dataset JSON file'
    )
    parser.add_argument(
        '--output-dir',
        type=str,
        required=True,
        help='Directory to save the deduplicated output'
    )
    parser.add_argument(
        '--threshold',
        type=float,
        default=0.9,
        help='Similarity threshold for deduplication'
    )
    parser.add_argument(
        '--workers',
        type=int,
        default=None,
        help='Number of worker processes (default: half of CPU cores)'
    )
    return parser.parse_args()

if __name__ == "__main__":
    multiprocessing.set_start_method('spawn', force=True)
    args = parse_args()
    process_data(args) 