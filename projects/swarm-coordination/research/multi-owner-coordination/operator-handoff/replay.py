#!/usr/bin/env python3
"""Serial selected-body task interruption, no device or ROS."""
from pathlib import Path
import hashlib,sys,tempfile,subprocess
p=Path(__file__).resolve().parent
u=Path(sys.argv[1])
def pin(name,sha):
    b=(u/name).read_bytes()
    assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==sha,name
    return b.decode()
m=pin('TaskManager.cpp','5e71c788c01d257a494a364a4f45a2f4e10042fa')
h=pin('RobotUpdateHandle.cpp','989012318cdbbd01d45604f7c8c05af09be078c1')
s=pin('RobotUpdateHandle.hpp','35f9e32e4d8ee2a724d28cff413ee984ee594efd')
assert 'mgr->interrupt_robot(' in h and 'Interruption interrupt(' in s
def body(key):
    a=m.index(key)
    return m[a:m.index('\n}',a)+2]
with tempfile.TemporaryDirectory() as d:
    d=Path(d)
    cc=d/'test.cc'
    cc.write_text('\n'.join([(p/'standins.inc').read_text(),
        *(body(key) for key in (
            'void TaskManager::Interruption::resume(',
            'TaskManager::Interruption::~Interruption()',
            'void TaskManager::interrupt_robot(',
            'void TaskManager::_process_robot_interrupts()',
            'std::function<void()> TaskManager::_robot_interruption_callback()')),
        (p/'compare.inc').read_text()]))
    subprocess.run(['c++','-std=c++20','-Wall','-Wextra','-Werror',cc,'-o',d/'replay'],check=True)
    subprocess.run([d/'replay'],check=True)
