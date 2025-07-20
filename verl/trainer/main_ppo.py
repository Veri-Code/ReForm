# Copyright 2024 Bytedance Ltd. and/or its affiliates
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
"""
Note that we don't combine the main with ray_trainer as ray_trainer is used by other main.
"""
from verl.trainer.ppo.ray_trainer import RayPPOTrainer
from verl import DataProto
import torch
from verl.utils.reward_score import naive_reward, subset_reward, formal_cot_oneshot_pure_remove
import os
import time
from pathos.multiprocessing import ProcessingPool as Pool
import random
import ray
@ray.remote
def compute_score_ray(input_tuple):
    return compute_score(input_tuple)

def compute_score(input_tuple):
    sequences_str, ground_truth, idx, exp_name, valid_response_length, data_source,reward_version,score_version, reward_type = input_tuple
    score = score_version[0]
    refine_score = score_version[1]
    if reward_type == "spec":
        score = subset_reward.compute_score(
            solution_str=sequences_str, 
            ground_truth=ground_truth, 
            index=idx, 
            exp_name=exp_name,
            score=score,
            refine_score=refine_score,
            version=reward_version,
            )
    elif reward_type == "intermediate":
        score = subset_reward.compute_intermediate_score(
            solution_str=sequences_str, 
            ground_truth=ground_truth, 
            index=idx, 
            exp_name=exp_name,
            score=score,
            refine_score=refine_score,
            version=reward_version,
            )
    elif reward_type == "formal_cot_simple":
        score = formal_cot_oneshot_pure_remove.compute_score(
            solution_str=sequences_str, 
            ground_truth=ground_truth, 
            index=idx, 
            exp_name=exp_name,
            version=reward_version,
            )
    elif reward_type == "formal_cot_spec":
        score = formal_cot_oneshot_pure_remove.compute_spec_score(
            solution_str=sequences_str, 
            ground_truth=ground_truth, 
            index=idx, 
            exp_name=exp_name,
            score=score,
            refine_score=refine_score,
            version=reward_version,
            )
    else:
        score = naive_reward.compute_score(
            solution_str=sequences_str, 
            ground_truth=ground_truth, 
            index=idx, 
            exp_name=exp_name
            )
    extra_info = None
    if isinstance(score, tuple):
        extra_info = score
        score = score[0]
    return score, valid_response_length - 1, sequences_str, data_source, extra_info


class RewardManager():
    """The reward manager."""

    def __init__(self, tokenizer, num_examine, exp_name, score_version, reward_version, reward_type) -> None:
        self.tokenizer = tokenizer
        self.num_examine = num_examine  # the number of batches of decoded responses to print to the console
        self.exp_name = exp_name
        self.reward_version = reward_version
        self.score_version = score_version
        self.reward_type = reward_type

    def __call__(self, data: DataProto, return_dict=False):
        """We will expand this function gradually based on the available datasets"""

        # If there is rm score, we directly return rm score. Otherwise, we compute via rm_score_fn
        if 'rm_scores' in data.batch.keys():
            return data.batch['rm_scores']

        reward_tensor = torch.zeros_like(data.batch['responses'], dtype=torch.float32)

        already_print_data_sources = {}

        # Prepare data for parallel processing
        tasks = []
        sequences_all = []
        valid_response_lengths = []
        for i in range(len(data)):
            data_item = data[i]  # DataProtoItem
            # data_item, tokenizer, num_examine, exp_name = input_tuple
            """Helper function to compute score in parallel."""
            prompt_ids = data_item.batch['prompts']
            prompt_length = prompt_ids.shape[-1]

            valid_prompt_length = data_item.batch['attention_mask'][:prompt_length].sum()
            valid_prompt_ids = prompt_ids[-valid_prompt_length:]

            response_ids = data_item.batch['responses']
            valid_response_length = data_item.batch['attention_mask'][prompt_length:].sum()
            valid_response_ids = response_ids[:valid_response_length]
            sequences = torch.cat((valid_prompt_ids, valid_response_ids))
            sequences_str = self.tokenizer.decode(sequences)
            ground_truth = data_item.non_tensor_batch['reward_model']['ground_truth']
            data_source = data_item.non_tensor_batch['data_source']
            idx = data_item.non_tensor_batch['index']
            tasks.append((sequences_str, ground_truth, idx, self.exp_name, valid_response_length, data_source,self.reward_version, self.score_version, self.reward_type))

        results = [compute_score_ray.remote(task) for task in tasks]
        results = ray.get(results)

        # Process the results
        extra_infos = []
        for i, (score, valid_response_length, sequences_str, data_source, extra_info) in enumerate(results):
            reward_tensor[i, valid_response_length] = score
            extra_infos.append(extra_info)
            if data_source not in already_print_data_sources:
                already_print_data_sources[data_source] = 0

            if already_print_data_sources[data_source] < self.num_examine:
                already_print_data_sources[data_source] += 1

        if not return_dict:
            return reward_tensor
        else:
            return {
                "reward_tensor": reward_tensor,
                "reward_extra_info": {},
                "details": extra_infos,
            }

import ray
import hydra

@hydra.main(config_path='config', config_name='ppo_trainer', version_base=None)
def main(config):
    run_ppo(config)

def run_ppo(config) -> None:
    # TODO(linjunrong.ocss884): this ENV is left for resolving SGLang conflict with ray devices
    # isolation, will solve in the future
    os.environ["ENSURE_CUDA_VISIBLE_DEVICES"] = os.environ.get('CUDA_VISIBLE_DEVICES', '')
    if not ray.is_initialized():
        # this is for local ray cluster
        ray.init(runtime_env={
            'env_vars': {
                'TOKENIZERS_PARALLELISM': 'true',
                'NCCL_DEBUG': 'WARN',
                'VLLM_LOGGING_LEVEL': 'WARN'
            }
        })

    runner = TaskRunner.remote()
    ray.get(runner.run.remote(config))


@ray.remote(num_cpus=1)  # please make sure main_task is not scheduled on head
class TaskRunner:

    def run(self, config):
        from verl.utils.fs import copy_to_local
        # print initial config
        from pprint import pprint
        from omegaconf import OmegaConf
        exp_name = config.trainer.experiment_name
        pprint(OmegaConf.to_container(config, resolve=True))  # resolve=True will eval symbol values
        OmegaConf.resolve(config)

        # download the checkpoint from hdfs
        local_path = copy_to_local(config.actor_rollout_ref.model.path)

        # instantiate tokenizer
        from verl.utils import hf_tokenizer, hf_processor
        trust_remote_code = config.data.get('trust_remote_code', False)
        tokenizer = hf_tokenizer(local_path, trust_remote_code=trust_remote_code)
        processor = hf_processor(local_path, use_fast=True)  # used for multimodal LLM, could be none

        # define worker classes
        if config.actor_rollout_ref.actor.strategy == 'fsdp':
            assert config.actor_rollout_ref.actor.strategy == config.critic.strategy
            from verl.workers.fsdp_workers import ActorRolloutRefWorker, CriticWorker
            from verl.single_controller.ray import RayWorkerGroup
            ray_worker_group_cls = RayWorkerGroup

        elif config.actor_rollout_ref.actor.strategy == 'megatron':
            assert config.actor_rollout_ref.actor.strategy == config.critic.strategy
            from verl.workers.megatron_workers import ActorRolloutRefWorker, CriticWorker
            from verl.single_controller.ray.megatron import NVMegatronRayWorkerGroup
            ray_worker_group_cls = NVMegatronRayWorkerGroup

        else:
            raise NotImplementedError

        from verl.trainer.ppo.ray_trainer import ResourcePoolManager, Role

        role_worker_mapping = {
            Role.ActorRollout: ray.remote(ActorRolloutRefWorker),
            Role.Critic: ray.remote(CriticWorker),
            # Role.RefPolicy: ray.remote(ActorRolloutRefWorker)
        }

        global_pool_id = 'global_pool'
        resource_pool_spec = {
            global_pool_id: [config.trainer.n_gpus_per_node] * config.trainer.nnodes,
        }
        mapping = {
            Role.ActorRollout: global_pool_id,
            Role.Critic: global_pool_id,
            # Role.RefPolicy: global_pool_id,
        }

        # we should adopt a multi-source reward function here
        # - for rule-based rm, we directly call a reward score
        # - for model-based rm, we call a model
        # - for code related prompt, we send to a sandbox if there are test cases
        # - finally, we combine all the rewards together
        # - The reward type depends on the tag of the data
        if config.reward_model.enable:
            if config.reward_model.strategy == 'fsdp':
                from verl.workers.fsdp_workers import RewardModelWorker
            elif config.reward_model.strategy == 'megatron':
                from verl.workers.megatron_workers import RewardModelWorker
            else:
                raise NotImplementedError
            role_worker_mapping[Role.RewardModel] = ray.remote(RewardModelWorker)
            mapping[Role.RewardModel] = global_pool_id
        reward_version = config.reward_model.reward_version
        score_version = config.reward_model.score_version
        reward_type = config.reward_model.reward_type
        reward_fn = RewardManager(
            tokenizer=tokenizer, 
            num_examine=0, 
            exp_name=exp_name, 
            score_version=score_version, 
            reward_version=reward_version, 
            reward_type=reward_type
        )

        #use reference model
        if config.algorithm.use_kl_in_reward or config.actor_rollout_ref.actor.use_kl_loss:
            role_worker_mapping[Role.RefPolicy] = ray.remote(ActorRolloutRefWorker)
            mapping[Role.RefPolicy] = global_pool_id

        val_reward_fn = RewardManager(
            tokenizer=tokenizer, 
            num_examine=1, 
            exp_name=exp_name, 
            score_version=score_version, 
            reward_version=reward_version, 
            reward_type=reward_type
        )

        resource_pool_manager = ResourcePoolManager(resource_pool_spec=resource_pool_spec, mapping=mapping)

        trainer = RayPPOTrainer(config=config,
                                tokenizer=tokenizer,
                                processor=processor,
                                role_worker_mapping=role_worker_mapping,
                                resource_pool_manager=resource_pool_manager,
                                ray_worker_group_cls=ray_worker_group_cls,
                                reward_fn=reward_fn,
                                val_reward_fn=val_reward_fn,
                                )
        trainer.init_workers()
        trainer.fit()


if __name__ == '__main__':
    main()
