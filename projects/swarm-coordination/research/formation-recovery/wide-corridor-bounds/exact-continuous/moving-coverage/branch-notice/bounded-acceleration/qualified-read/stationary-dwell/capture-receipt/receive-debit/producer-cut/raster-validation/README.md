# Actual headless depth rendering through the qualification test

[Raster_To_Branch.tex](Raster_To_Branch.tex) rasterizes authored planar scenes,
runs the exact pinned Ogre2 vertex and fragment depth passes, and feeds
selected rendered pixels through the native source and radio slices.
An upstream renderer cutoff or actual occlusion removes the far cue
before any proposed raw read. The independent ray oracle also checks a
narrow obstacle missed at one camera position.

Inputs for rasterization are in INPUTS.tsv. SENSOR_IMPORTS.tsv and the
inherited manifests in sensor/ locate the earlier source slices. Put the
selected-source shim inputs under their declared aliases and run sh run.sh.
The exact captured outputs for this Mesa configuration are raster.json
and joined.json; built-in checks test tolerances and classifications even
on a different driver. The Space ZIP includes all needed source inputs.

Requires Python 3, Git, C++17/20, software Mesa EGL/OpenGL and a compiler.
No actual CoSTAR stack or frame geometry from an independent mission.

[Active camera aperture](active-aperture/README.md) derives what displacement
and stationary pose qualification are actually needed to restore the occluded
far cue, retaining the old receiver duties.
