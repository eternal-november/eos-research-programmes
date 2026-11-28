import bridge,json,sys
from pathlib import Path
binary,sites,posefile=sys.argv[1:]
bridge.cases={(r["gate"],r["mode"]):r for r in json.loads(Path(posefile).read_text())}
print(json.dumps(bridge.trace(binary,sites,0,2,3,6,'before','checked','clearance','after',0,'resource-scoped'),sort_keys=True))
