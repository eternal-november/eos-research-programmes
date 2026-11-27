# Cave depth bridge retirement and point clipping

[Technical note](Depth_Bridge_Retirement.tex). In the reference Melodic
bridge, the CoSTAR depth-image handler asks for a native subscription
at construction, without waiting for a ROS recorder. Under the selected
Transport 9 publisher path, a **registered** depth bridge can be locally
absent from the process list while its old subscription still makes
fresh 37 m point samples infinite. Delivery of a named termination for
the exact subscriber clears the retained entry; the process-only timeout
or BYE callback does not. This can happen even after a new bridge briefly
registers and then ends normally under a different process identity.

This is an offline source replay: selected bridge constructor, callback
emission, publisher ledger and pixel-packing code, with ordinary
lifecycle states and fresh samples supplied to the harness. It does not
start Gazebo or ROS, send discovery messages, fix a deployed package,
or establish loaded image, registration latency, or actual cave visibility.
Use the [Space archive](https://chatgpt.com/space/page_f5a09a52f6b881919b10d91ecf2caa80)
to run `sh run.sh | cmp expected.txt -` without network. The archive
contains all inputs listed in `LIFECYCLE_INPUTS.tsv`, including exact
#739 extraction source. Requires Python 3 and C++17. Do not disable assertions.

[Cut qualification](frame-guard-cuts/README.md): matching connection bits
bracketing a frame do not exclude a change and reversal between polls.
A bounded transition token gives an exact discriminator in the declared
serial source model, but is not furnished by stock Transport.
