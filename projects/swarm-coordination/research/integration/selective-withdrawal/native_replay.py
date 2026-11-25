from hashlib import sha1
from pathlib import Path
import re
import shutil
import subprocess
import tempfile

SOURCE = {
    "DefaultVehicleController.java": "9fd27d860a37b5b751361be60212d8a7bf921b23",
    "CommandProcessingTracker.java": "d98fd28423969e13975eccb2d061470862739501",
    "PeripheralInteractor.java": "2bd407409d0ea1d4d8cc7fbc4f6c220669e78988",
}
contents = {}
for path, expected in SOURCE.items():
    raw = Path(path).read_bytes()
    assert sha1(f"blob {len(raw)}\0".encode()+raw).hexdigest()==expected, path
    contents[path] = raw.decode()

def exact(name, names):
    src = contents[name]
    selected = []
    for name in names:
        hits = list(re.finditer(r'^  (?:private|public) [^\n]*\b'+name+r'\([^;\{]*\) \{', src, re.M))
        assert len(hits)==1, (name,len(hits))
        m = hits[0]
        depth = 1
        for i, x in enumerate(src[m.end():], start=m.end()):
            depth += (x=='{') - (x=='}')
            if not depth:
                selected.append(src[m.start():i+1])
                break
        else:
            raise AssertionError(name)
    return "\n\n".join(selected)

template = Path("NativeHarness.java.in").read_text()
for marker, src, methods in (
 ("CONTROLLER", "DefaultVehicleController.java",
  "abortTransportOrder clearDriveOrder abortDriveOrder clearCommandQueue withdrawPendingResourceAllocations sendCommandOrStopSending checkForPendingCommands"),
 ("TRACKER", "CommandProcessingTracker.java",
  "driveOrderAborted getAllocatedResourcesAhead hasCommandsToBeSent isDriveOrderFinished commandSendingStopped"),
 ("PERIPHERAL", "PeripheralInteractor.java", "clear"),
):
    template=template.replace("/* "+marker+" */", exact(src,methods.split()))
with tempfile.TemporaryDirectory() as directory:
    path=Path(directory)/"NativeHarness.java"
    path.write_text(template)
    subprocess.run([shutil.which("java") or "java", str(path)],check=True)
