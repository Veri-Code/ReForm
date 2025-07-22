import json
from collections import Counter
import matplotlib.pyplot as plt
import numpy as np
from utils import *

sys.path.append(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

def format_tuple_label(t) -> str:
    """
    Format a tuple or list like ('int',) or ['int'] to 'int', and ('int', 'int') to 'int, int'.
    If the value is None, empty string, or 'None', convert it to string 'None'.
    """
    if isinstance(t, (list, tuple)):
        if len(t) == 1:
            v = t[0]
            if v is None or v == '' or v == 'None':
                return 'None'
            return str(v)
        return ', '.join('None' if (x is None or x == '' or x == 'None') else str(x) for x in t)
    # If not list/tuple, just convert to string
    return str(t)

def analyze_io_patterns(data: list[dict]) -> tuple[Counter, Counter, Counter, Counter, Counter, list]:
    """
    Analyze input and output type patterns from the data.
    Returns: (input_patterns, output_patterns, return_count_patterns, input_count_patterns, code_lines_patterns, filtered_data)
    """
    code_lines_patterns = Counter()
    filtered_data = []
    # First count code lines distribution for all samples and filter out samples with <10 lines
    for item in data:
        code = item.get('code', '')
        code_lines = len([line for line in code.split('\n') if line.strip()])
        code_lines_patterns[code_lines] += 1
        if code_lines >= 10:
            filtered_data.append(item)
    # Only analyze IO patterns for filtered_data
    input_patterns = Counter()
    output_patterns = Counter()
    return_count_patterns = Counter()
    input_count_patterns = Counter()
    for item in filtered_data:
        io_types = extract_io_types(item['signature'])
        io_dict = convert_io_types_to_dict(io_types)
        input_pattern = tuple(io_dict['Input'])
        if not input_pattern or input_pattern == ('',):
            input_pattern = ('None',)
        output_pattern = tuple(io_dict['Output'])
        # Input parameter count
        if input_pattern == ('None',):
            input_count = 0
        else:
            input_count = len(input_pattern)
        # Output parameter count
        if output_pattern == ('None',):
            return_count = 0
        else:
            return_count = len(output_pattern)
        input_patterns[input_pattern] += 1
        output_patterns[output_pattern] += 1
        return_count_patterns[return_count] += 1
        input_count_patterns[input_count] += 1
    return input_patterns, output_patterns, return_count_patterns, input_count_patterns, code_lines_patterns, filtered_data

def plot_io_type_patterns(input_patterns: Counter, output_patterns: Counter, save_path: str = None, top_n: int = 25):
    """
    Plot input and output type patterns in one image.
    """
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(14, 10))

    # --- Input patterns ---
    input_items = input_patterns.most_common(top_n)
    input_types = [item[0] for item in input_items]
    input_counts = [item[1] for item in input_items]
    input_labels = [format_tuple_label(t) for t in input_types]

    ax1.barh(range(len(input_types)), input_counts)
    ax1.set_title(f'Top {top_n} Input Type Patterns')
    ax1.set_xlabel('Count')
    ax1.set_ylabel('Input Type Pattern')
    ax1.set_yticks(range(len(input_types)))
    ax1.set_yticklabels(input_labels, fontsize=10)
    ax1.invert_yaxis()

    # --- Output patterns ---
    output_items = output_patterns.most_common(top_n)
    output_types = [item[0] for item in output_items]
    output_counts = [item[1] for item in output_items]
    output_labels = [format_tuple_label(t) for t in output_types]

    ax2.barh(range(len(output_types)), output_counts)
    ax2.set_title(f'Top {top_n} Output Type Patterns')
    ax2.set_xlabel('Count')
    ax2.set_ylabel('Output Type Pattern')
    ax2.set_yticks(range(len(output_types)))
    ax2.set_yticklabels(output_labels, fontsize=10)
    ax2.invert_yaxis()

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path)
    else:
        plt.show()

def plot_io_patterns(input_patterns: Counter, output_patterns: Counter, return_count_patterns: Counter, input_count_patterns: Counter, save_path: str = None, top_n: int = 25):
    """
    Create bar plots for input/output patterns, return count, and input count distribution.
    """
    fig, (ax1, ax2, ax3, ax4) = plt.subplots(4, 1, figsize=(14, 20))

    # --- Input patterns ---
    input_items = input_patterns.most_common(top_n)
    input_types = [item[0] for item in input_items]
    input_counts = [item[1] for item in input_items]
    input_labels = [format_tuple_label(t) for t in input_types]

    ax1.barh(range(len(input_types)), input_counts)
    ax1.set_title(f'Top {top_n} Input Type Patterns')
    ax1.set_xlabel('Count')
    ax1.set_ylabel('Input Type Pattern')
    ax1.set_yticks(range(len(input_types)))
    ax1.set_yticklabels(input_labels, fontsize=10)
    ax1.invert_yaxis()  # Highest count on top

    # --- Output patterns ---
    output_items = output_patterns.most_common(top_n)
    output_types = [item[0] for item in output_items]
    output_counts = [item[1] for item in output_items]
    output_labels = [format_tuple_label(t) for t in output_types]

    ax2.barh(range(len(output_types)), output_counts)
    ax2.set_title(f'Top {top_n} Output Type Patterns')
    ax2.set_xlabel('Count')
    ax2.set_ylabel('Output Type Pattern')
    ax2.set_yticks(range(len(output_types)))
    ax2.set_yticklabels(output_labels, fontsize=10)
    ax2.invert_yaxis()

    # --- Return count patterns ---
    return_count_items = sorted(return_count_patterns.items())
    return_counts = [item[0] for item in return_count_items]
    count_frequencies = [item[1] for item in return_count_items]

    ax3.bar(return_counts, count_frequencies)
    ax3.set_title('Return Value Count Distribution')
    ax3.set_xlabel('Number of Return Values')
    ax3.set_ylabel('Count')
    ax3.set_xticks(return_counts)

    # --- Input count patterns ---
    input_count_items = sorted(input_count_patterns.items())
    input_counts_x = [item[0] for item in input_count_items]
    input_counts_y = [item[1] for item in input_count_items]

    ax4.bar(input_counts_x, input_counts_y)
    ax4.set_title('Input Parameter Count Distribution')
    ax4.set_xlabel('Number of Input Parameters')
    ax4.set_ylabel('Count')
    ax4.set_xticks(input_counts_x)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path)
    else:
        plt.show()

def save_top_input_pattern_samples(data: list[dict], input_patterns: Counter, top_n: int, output_path: str):
    # Get Top-N Input Patterns
    top_input_patterns = set([pattern for pattern, _ in input_patterns.most_common(top_n)])
    # Only keep samples belonging to Top-N patterns
    filtered_data = []
    for item in data:
        io_types = extract_io_types(item['signature'])
        io_dict = convert_io_types_to_dict(io_types)
        input_pattern = io_dict['Input']
        if input_pattern in top_input_patterns:
            filtered_data.append(item)
    # Write the filtered samples to a new jsonl file
    with open(output_path, 'w', encoding='utf-8') as f:
        for entry in filtered_data:
            f.write(json.dumps(entry, ensure_ascii=False) + '\n')
    print(f"Number of samples with Top-{top_n} Input Type Patterns: {len(filtered_data)}")

def plot_io_count_patterns(return_count_patterns: Counter, input_count_patterns: Counter, save_path: str = None):
    """
    Plot input parameter count and return value count distributions in one image.
    """
    fig, (ax1, ax2) = plt.subplots(2, 1, figsize=(10, 8))

    # --- Return count patterns ---
    return_count_items = sorted(return_count_patterns.items())
    return_counts = [item[0] for item in return_count_items]
    count_frequencies = [item[1] for item in return_count_items]

    ax1.bar(return_counts, count_frequencies)
    ax1.set_title('Return Value Count Distribution')
    ax1.set_xlabel('Number of Return Values')
    ax1.set_ylabel('Count')
    ax1.set_xticks(return_counts)

    # --- Input count patterns ---
    input_count_items = sorted(input_count_patterns.items())
    input_counts_x = [item[0] for item in input_count_items]
    input_counts_y = [item[1] for item in input_count_items]

    ax2.bar(input_counts_x, input_counts_y)
    ax2.set_title('Input Parameter Count Distribution')
    ax2.set_xlabel('Number of Input Parameters')
    ax2.set_ylabel('Count')
    ax2.set_xticks(input_counts_x)

    plt.tight_layout()
    if save_path:
        plt.savefig(save_path)
    else:
        plt.show()

def plot_code_lines_distribution(code_lines_patterns: Counter, save_path: str = None, removed_threshold: int = 10):
    """
    Plot code lines count distribution with automatic binning and highlight removed bins.
    """
    all_counts = []
    for lines, freq in code_lines_patterns.items():
        all_counts.extend([lines] * freq)
    all_counts = np.array(all_counts)

    plt.figure(figsize=(14, 6))
    n, bins, patches = plt.hist(all_counts, bins='auto', edgecolor='black', align='left')

    # Highlight removed bins (code lines < removed_threshold)
    label_set = False
    for i, patch in enumerate(patches):
        left = bins[i]
        right = bins[i+1]
        if right <= removed_threshold:
            patch.set_facecolor('red')
            if not label_set:
                patch.set_label('Removed (<10 lines)')
                label_set = True
    # Only add legend if label was set
    handles, labels = plt.gca().get_legend_handles_labels()
    if handles:
        plt.legend()

    plt.title('Code Lines Count Distribution (Auto Binned, <10 lines removed)')
    plt.xlabel('Number of Code Lines')
    plt.ylabel('Count')
    plt.grid(axis='y', linestyle='--', alpha=0.7)
    plt.tight_layout()
    if save_path:
        plt.savefig(save_path)
    else:
        plt.show()

def main():
    # Parse the JSONL file
    data = jsonl_parser('../../raw_code/reformed_leetcodes.jsonl')
    
    # Analyze patterns (filtered_data only keeps code lines >= 10)
    input_patterns, output_patterns, return_count_patterns, input_count_patterns, code_lines_patterns, filtered_data = analyze_io_patterns(data)
    
    # Print statistics
    print("\nInput Type Patterns:")
    for pattern, count in input_patterns.most_common():
        print(f"{format_tuple_label(pattern)}: {count}")
    
    print("\nOutput Type Patterns:")
    for pattern, count in output_patterns.most_common():
        print(f"{format_tuple_label(pattern)}: {count}")
    
    print("\nReturn Value Count Distribution:")
    for count, frequency in sorted(return_count_patterns.items()):
        print(f"{count} return value(s): {frequency} functions")
    
    print("\nInput Parameter Count Distribution:")
    for count, frequency in sorted(input_count_patterns.items()):
        print(f"{count} input parameter(s): {frequency} functions")
    
    print("\nCode Lines Count Distribution:")
    for count, frequency in sorted(code_lines_patterns.items()):
        print(f"{count} code lines: {frequency} functions")
    
    # Save IO type pattern plots
    plot_io_type_patterns(
        input_patterns, output_patterns,
        '../../plots/io_patterns.png'
    )
    # Save IO count pattern plots
    plot_io_count_patterns(
        return_count_patterns, input_count_patterns,
        '../../plots/io_counts.png'
    )
    # Save code lines distribution plot (highlight removed bins)
    plot_code_lines_distribution(
        code_lines_patterns,
        '../../plots/code_lines.png',
        removed_threshold=10
    )

    # Save filtered samples (only code lines >= 10)
    save_top_input_pattern_samples(
        filtered_data,
        input_patterns,
        top_n=25,
        output_path='../../raw_code/reformed_leetcodes_top25input.jsonl'
    )

if __name__ == "__main__":
    main()
