"""Re-use the upstream hash-checked cuts, adding the native pose-cache statements."""
from pathlib import Path
s=Path("src0").read_text()
left=s.index("  auto updatePoseFunc")
right=s.index("  broker.SetPoseUpdateFunction",left)
Path("pose.inc").write_text(s[left:right])
left=s.index("  // Store sim time if present")
right=s.index("  // Update the visibility graph",left)
Path("frame.inc").write_text(s[left:right])
