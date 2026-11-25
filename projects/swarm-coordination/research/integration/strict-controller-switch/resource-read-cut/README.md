# Resource-manager observation while another device changes state

[Proof, four recorded cuts and scope](Resource_Read_Cut.tex). The
healthy-cycle and manager-lock cases have identical read/write status
but different executed operations. The component-lock control
shows why scoping the input resource alone does not avoid a
manager-wide lock.

Supply the source file from [SOURCE.tsv](SOURCE.tsv) under its original
basename and run:

    sh replay.sh /path/to/upstream | cmp results.txt -

Requires Python 3 and a C++17 compiler. The original four methods are
compiled with stub devices and controlled lock timings, not ROS or
real actuators. The replay verifies the source blob first.
