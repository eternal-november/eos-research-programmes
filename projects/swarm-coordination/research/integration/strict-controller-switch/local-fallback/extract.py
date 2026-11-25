"""Pin sources and select control-flow slices without executing ROS or hardware."""
import hashlib
from pathlib import Path
import sys

def read_pinned(path, oid):
    data=Path(path).read_bytes()
    assert hashlib.sha1(f"blob {len(data)}\0".encode()+data).hexdigest()==oid
    return data.decode()

def fn(source, name, indent=""):
    i=source.index(name)
    j=source.index("\n"+indent+"}",i)+len(indent)+2
    return source[i:j]

base=Path(sys.argv[1])
m=read_pinned(base/"controller_manager.cpp","07d3fa768237875322ddea775386faceb46ebb50")
h=read_pinned(base/"controller_manager.hpp","43a76b40e31e038c2798c036f7b3b1c9b9c7c9fa")
a=m.index("  if (!rt_buffer_.deactivate_controllers_list.empty())",m.index("ControllerManager::update("))
z=m.index("  PUBLISH_ROS2_CONTROL_INTROSPECTION_DATA_ASYNC",a)
ga=m.index("    if (\n      switch_params_.do_switch && !switch_params_.activate_asap &&")
gz=m.index("    if (is_controller_active",ga)
g=m[ga:gz]
assert "switch_params_.skip_cycle(loaded_controller)" in g and "continue;" in g
fa=m.index("        if (controller_ret != controller_interface::return_type::OK)",ga)
fb=m.index("\n        }",fa)+10
f=m[fa:fb]
assert f.rstrip().endswith("}") and "ret = controller_ret;" in f
lines=[
    fn(h,"bool skip_cycle(", "    "),
    fn(m,"bool controller_name_compare("),
    fn(m,"void get_active_controllers_using_command_interfaces_of_controller("),
    fn(m,"void extract_command_interfaces_for_controller("),
    fn(m,"void get_controller_list_command_interfaces("),
    fn(m,"void ControllerManager::switch_controller_service_cb("),
    fn(m,"void ControllerManager::read("),
    fn(m,"void ControllerManager::perform_hardware_command_mode_change("),
]
# Use separate includes for the class-half declaration/definition and exact
# selected bodies. The skip snippet stays inside the authored mock loop.
for name,code in zip(("skip_member.inc","upstream.inc","skip_guard.inc","update_tail.inc","collect_error.inc"),
                     (lines[0],"\n\n".join(lines[1:]),g,m[a:z],f)):
    (Path(sys.argv[2])/name).write_text(code+"\n")
