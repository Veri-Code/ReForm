# Dafny Process Documentation

This folder provides all scripts and data related to the preparation and evaluation of datasets for Supervised Fine-Tuning (SFT) and benchmarking with Dafny.

## Folder Overview

- **src/**: Contains all scripts for processing, cleaning, converting, and preparing datasets used for SFT. This is the main working directory for generating SFT-ready data from various sources.
- **raw_dataset/**: Stores the raw data files that serve as the source for SFT dataset conversion. These files are not directly used for training but are processed by scripts in `src/` to produce the final SFT datasets.
- **DafnyComp/**: Contains scripts and resources for constructing the evaluation benchmark. This includes code for composing, filtering, and synthesizing Dafny programs, as well as tools for evaluating model performance on benchmark tasks.

## Detailed File Descriptions

### src/ — SFT Dataset Processing Scripts

- **reformat2infer.py**  
  Converts SFT-format data into a format suitable for inference and evaluation. Reads a JSON file, processes each entry, and outputs a new JSON file with fields required for downstream inference tasks.

- **extract_raw_dafny.py**  
  Extracts Dafny code snippets from SFT or inference-format data. Supports both SFT and inference data structures, and outputs a JSON file containing only the Dafny code for further processing or analysis.

- **build_sft_data_from_json.py**  
  Converts raw or intermediate JSON data into the final SFT training format. Handles code cleaning, annotation generation, and field mapping. Supports batch processing and can be customized for different data sources. (The outputs are located in `LLaMA-Factory/data/processed_data`)

- **build_grid_search_cfgs.py**  
  Automatically generates multiple training configuration YAML files for grid search experiments. Reads a base config, modifies key hyperparameters (like learning rate, epochs, etc.), and saves the new configs for batch training. (The outputs are located in `LLaMA-Factory/examples/grid_search`)

- **run_advanced_dedup.py**  
  Performs advanced deduplication on datasets using MinHash LSH and string similarity. Removes near-duplicate or highly similar code samples to improve data quality and reduce redundancy.

- **filter_trivial_compiled.py**  
  Filters out code samples that are too trivial (e.g., too few lines of code) from the dataset. Ensures that only meaningful and non-trivial Dafny code is retained for training or evaluation.

#### src/utils/ — Utility Functions

- **basic.py**  
  Provides general-purpose file parsing and saving utilities, including support for JSON, JSONL, and Parquet formats. Also includes helpers for file format detection and progress reporting.

- **process.py**  
  Contains code cleaning and transformation utilities, such as removing comments, dependencies, and specific Dafny annotations. Also provides functions for code verification, parallel processing, and extraction of code segments.

#### src/scripts/ — Training Script Templates

- **run_train_gird_search_sample.sh**  
  Shell script for batch training using grid search configurations. Iterates over multiple config files and datasets, launching training jobs and managing logs.

- **run_train_sample.sh**  
  Shell script for running SFT training on multiple datasets or models. Dynamically updates config files and launches training jobs for each combination.

### DafnyComp/src/compose — Composition and Filtering Scripts

- **1in1out_filter.py**  
  Filters samples to retain only those with single integer input and output types. Useful for focusing on simple function signatures in composition tasks. (The outputs are located in `DafnyComp/raw_code`)

- **cc_shard_py.py**  
  Analyzes code complexity (cyclomatic complexity and Halstead metrics) for code samples, categorizes them by complexity level, and outputs statistics and histograms for further analysis. (The plots are located in `DafnyComp/plots`)

- **check_syntax.py**  
  Checks the syntax of generated Python files using flake8 and autopep8. Attempts to auto-fix formatting issues and logs all results, helping to ensure code quality in composed programs. (The bugs are located in `DafnyComp/logs/bugs`)

- **constraint_analyzer.py**  
  Analyzes and propagates input/output constraints through composed function chains. Detects constraint conflicts and logs analysis results for debugging and validation. (The conflicts are located in `DafnyComp/logs/conflicts`)

- **extract_reformat.py**  
  Extracts methods from Python classes, removes 'self' references, and reformats code for use in composition pipelines. Also handles renaming and code transformation for compatibility. (The outputs are located in `DafnyComp/raw_code`)

- **static_filter.py**  
  Analyzes and filters code samples based on static properties such as input/output type patterns and code length. Generates statistics and plots for dataset analysis. (The plots are located in `DafnyComp/plots`)

- **composition_testcases_dy.py**  
  Generates and manages test cases for composed functions, including code quality checks, import management, and template-based code generation for evaluation.

- **template.py**  
  Defines template patterns for function composition, including various DAG (Directed Acyclic Graph) structures and code generation utilities for composing multiple functions.

- **testcase_filter.py**  
  Filters test cases based on root function input/output constraints, validates test cases against constraints, and manages execution and error logging for composed programs. (Samples with no test case are located in `DafnyComp/logs/no_testcases`)

- **utils.py**  
  Provides shared utilities for code analysis, import management, constraint extraction, and code transformation used throughout the composition pipeline.

> **Tip:** The typical processing order for these scripts is: \
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`extract_reformat.py` → `1in1out_filter.py` → `composition_testcases_dy.py` → `check_syntax.py` → `constraint_analyzer.py` → `testcase_filter.py`.

### DafnyComp/src/synthesis — Python-to-Dafny Conversion and Evaluation Scripts

- **python2dafny_utils.py**  
  Core utilities for converting Python code to Dafny, including prompt construction for LLMs, verification routines, and result extraction. Supports both single-step and multi-step conversion workflows.

- **convert_python2dafny.py**  
  Batch conversion script for translating multiple Python files to Dafny using LLMs and verification tools. Handles directory traversal, result management, and supports both single-step and multi-step conversion modes.

- **API_Test_Eval_Json.py.py**  
  Evaluates LLMs on Dafny annotation tasks by generating prompts, calling the model, and collecting results for benchmarking. Supports parallel execution and result aggregation.

- **suc.py**  
  Collects and organizes successfully translated Dafny code samples, copying verified code and corresponding Python files to a designated directory for further analysis or benchmarking.

- **collect_dafny_files.py**  
  Recursively collects all verified Dafny code files from a directory, aggregates them into a single JSON file for downstream evaluation or dataset construction.

> **Tip:** 1. The typical processing order for these scripts is:\
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;`convert_python2dafny.py` → `suc.py` → `collect_dafny_files.py`.\
> &nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;2. The generation process requires LLM API calls. Please modify the `APIManager` class in `DafnyComp/src/synthesis/python2dafny_utils.py` according to your API platform.

**Note**: The `DafnyComp/code_wspec` directory contains the converted Python-Dafny code pairs (`DafnyComp/code_wspec/Chain_300`) as well as the extracted JSON file (`DafnyComp/code_wspec/DafnyComp_chain300.json`).

## Usage Notes

- To prepare SFT datasets, use the scripts in the `src/` directory. These scripts take raw data from `raw_dataset/` and output processed data suitable for SFT training.
- For evaluation and benchmark construction, refer to the tools and scripts in `DafnyComp/`.
- Each script is documented with comments to facilitate understanding and further development.

If you need more details about a specific script or workflow, please refer to the script's comments or open an issue for further clarification. 