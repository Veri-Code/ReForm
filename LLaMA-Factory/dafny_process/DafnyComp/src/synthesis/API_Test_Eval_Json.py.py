import json
import multiprocessing as mp
from tqdm import tqdm
from python2dafny_utils import APIManager, extract_dafny_code

# model_name = "gpt-4o"
# model_name = "claude-sonnet-4-20250514"
# model_name = "gemini-2.5-flash"
# model_name = "gemini-2.5-pro"
# model_name = "deepseek-r1"
# model_name = "gpt-4.1"
# model_name = "o4-mini"
# model_name = "grok-4"

def gpt_worker_single(args: tuple) -> dict:
    row_dict, shot_idx = args
    api_manager = APIManager()
    instruction = "Given a Dafny program with function signature, preconditions, postconditions, and code, but with annotations missing. Please return a complete Dafny program with the strongest possible annotation (loop invariants, assert statements, etc.) filled back in. Do not explain or output any text. If you have to explain, put all explanations in comments form. There should only be code body in your output. Please use exactly the same function signature, preconditions, and postconditions. Do not ever modify the given lines. Below is the program:\n```dafny\n"
    input = row_dict.get('org_input', '')
    messages = [
        {"role": "system", "content": "You are an expert in Dafny. You will be given tasks dealing with Dafny programs including precise annotations. You should only return code body in all circumstances. No text is allowed."},
        {"role": "user", "content": instruction + input}
    ]
    org_input_id = row_dict.get('org_input_id', 0)
    try:
        gpt_reply = api_manager.call_llm(messages, model=model_name)
    except Exception as e:
        gpt_reply = f"ERROR: {e}"
    return {
        "org_input": row_dict.get('org_input', ''),
        "gt_output": row_dict.get('gt_output', None),
        "llm_input": instruction + input + "/n```",
        "dafny_input": extract_dafny_code(gpt_reply),
        "output": {
            "llm_response": gpt_reply,
            "dafny_response": {
                "status": "",
                "dafny_response": ""
            }
        },
        "stage_tag": "not_started",
        "org_input_id": org_input_id,
        "self_id": org_input_id * 10000 + shot_idx,
        "self_tag": row_dict.get('self_tag', "")
    }
    
if __name__ == "__main__":
    json_path = '../../code_wspec/dfyautospec_chain300_partial.json'
    output_json = f'../../code_wspec/dfyautospec_chain300_{model_name}_results.json'
    print(f"Using model: {model_name}")
    print(f"Using json: {json_path}")
    print(f"Using output: {output_json}")

    with open(json_path, 'r', encoding='utf-8') as f:
        data_list = json.load(f)

    shot_number = 8
    tasks = []
    for row_dict in data_list:
        for shot_idx in range(shot_number):
            tasks.append((row_dict, shot_idx))

    num_workers = max(8, mp.cpu_count())
    with mp.Pool(processes=num_workers) as pool:
        all_results = list(tqdm(pool.imap_unordered(gpt_worker_single, tasks), total=len(tasks)))

    with open(output_json, 'w', encoding='utf-8') as f:
        json.dump(all_results, f, ensure_ascii=False, indent=2)

    print(f"All Done. Results saved to {output_json}") 
    