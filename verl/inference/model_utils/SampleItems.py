import json
from dataclasses import dataclass, asdict
MULTIPLICATION_CONSTANT = 10000

@dataclass
class DafnyResponse:
    status: str = ''
    dafny_response: str = ''

@dataclass
class OutputItem:
    llm_response: str = ''
    dafny_response: DafnyResponse = DafnyResponse()

@dataclass
class SampleItem:
    org_input: str = ''
    gt_output: str = ''
    llm_input: str = ''
    dafny_input: str = ''
    output: OutputItem = OutputItem()
    stage_tag: str = 'not_started'
    org_input_id: int = -1
    self_id: int = -1 * MULTIPLICATION_CONSTANT
    self_tag: str = ''

def save_to_json(filename, sample_items):
    with open(filename, 'w', encoding='utf-8') as f:
        json.dump(sample_items, f, default=lambda o: asdict(o), ensure_ascii=False, indent=4)


def load_from_json(filename):
    with open(filename, 'r', encoding='utf-8') as f:
        data = json.load(f)
        return_list=list()
        for item in data:
            dafny_response = item['output']['dafny_response']
            output = OutputItem(llm_response = item['output']['llm_response'], dafny_response = DafnyResponse(status = dafny_response['status'], dafny_response = dafny_response['dafny_response']))
            current_item = SampleItem(**item)
            current_item.output = output
            return_list.append(current_item)

        return return_list

class SampleItemList(list):
    def __init__(self, *args):
        super().__init__(*args)
        self.id_counter = 0

    def append(self, item):
        item.id = self.id_counter
        self.id_counter += 1
        super().append(item)

    def save_to_json(self, filename):
        save_to_json(filename, self)
    
    def load_from_json(self, filename):
        sample_items = load_from_json(filename)
        self.extend(sample_items)


