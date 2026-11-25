# Handoff receipts across two native sources

[Scope and findings](Native_Handoff_Receipts.tex) · [frozen receiver contract](FREEZE.txt).

The receiver is the same in the warehouse and railway control. The adapters execute the selected native methods and use a different physical event for each task. This is authored source calibration, not an independently selected test.

Use the following exact pinned source files. `replay.py` checks every Git blob before extraction.

- `warehouse.py`: [RWARE warehouse.py](https://github.com/semitable/robotic-warehouse/blob/96fbc64e3eae5fee915e0d390f864fa06ddccd47/rware/warehouse.py).
- `rail.py`: [Flatland rail_env.py](https://github.com/flatland-association/flatland-rl/blob/4856ebfe268d092d787d6b8536791a4fddb30772/flatland/envs/rail_env.py).
- `agent_chains.py`: [Flatland agent_chains.py](https://github.com/flatland-association/flatland-rl/blob/4856ebfe268d092d787d6b8536791a4fddb30772/flatland/envs/agent_chains.py).
- `resource.py`: [Flatland grid_resource_map.py](https://github.com/flatland-association/flatland-rl/blob/4856ebfe268d092d787d6b8536791a4fddb30772/flatland/core/grid/grid_resource_map.py).
- `agents.py`: [Flatland agent_utils.py](https://github.com/flatland-association/flatland-rl/blob/4856ebfe268d092d787d6b8536791a4fddb30772/flatland/envs/agent_utils.py).
- `actions.py`: [Flatland rail_env_action.py](https://github.com/flatland-association/flatland-rl/blob/4856ebfe268d092d787d6b8536791a4fddb30772/flatland/envs/rail_env_action.py).

```sh
PYTHONHASHSEED=0 python3 -B replay.py /path/to/pinned/sources | cmp - results.json
sha256sum -c freeze.sha256
```

NumPy only. The Space archive includes the source files and the two earlier warehouse harnesses needed for independent local replay. This does not run full Flatland, its reward function, Gym, or a full warehouse environment.
