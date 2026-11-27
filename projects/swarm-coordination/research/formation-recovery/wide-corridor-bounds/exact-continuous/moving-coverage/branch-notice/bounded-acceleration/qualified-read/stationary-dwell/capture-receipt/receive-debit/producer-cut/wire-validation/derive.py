"""Selected pinned depth metadata -> ROS -> PCL contract test."""
from hashlib import sha1
from pathlib import Path as P
for l in P('WIRE_INPUTS.tsv').read_text().splitlines():
    f,_,_,_,k=l.split('\t')
    b=P(f).read_bytes()
    assert sha1(f'blob {len(b)}\0'.encode()+b).hexdigest()==k
def cut(f,start,end='\n}'):
    s=P(f).read_text()
    i=s.index(start)
    return s[i:s.index(end,i)+len(end)]
h=P('../rgbd_probe.cpp').read_text().split('int main(){',1)[0]
p=h.index('struct Field ')
q=h.index('struct PointCloudPacked',p)
h=h[:p]+'''struct Field {
 enum Type{INT8,UINT8,INT16,UINT16,INT32,UINT32,FLOAT32,FLOAT64};
 int k;
 unsigned offset()const{return unsigned(k)*4;}
 unsigned count()const{return 1;}
 Type datatype()const{return FLOAT32;}
 std::string name()const{return std::string(1,"xyz"[k]);}
};
'''+h[q:]
h=h.replace(' unsigned w;',''' using Field=msgs::Field;
 unsigned w;
 bool dense{};
 int header()const{return 0;}
 int field_size()const{return 3;}
 bool is_dense()const{return dense;}
 void set_is_dense(bool b){dense=b;}''',1)
h=h.replace('std::string data;','std::string blob;\n const std::string& data()const{return blob;}').replace('return &data;', 'return &blob;').replace('p.data.data()', 'p.data().data()')
h=h.replace(' Connected depthPub,pointPub;', ' Connected depthPub,pointPub;\n msgs::PointCloudPacked pointMsg{3};')
h=h.replace('#include "selected.inc"', '#include "../selected.inc"')
P('sensor_base.inc').write_text(h)
s=P('../sensor.cc').read_text()
a=s.index('this->dataPtr->pointMsg.set_is_dense(true);')
b=s.index(';',a)+1
P('dense_flag.inc').write_text(s[a:b]+'\n')
r=cut('ros.src','void\nconvert_ign_to_ros(\n  const ignition::msgs::PointCloudPacked & ign_msg,')
meta=cut('pcl_ros.src','void copyPointCloud2MetaData(const sensor_msgs::PointCloud2','\n  }')
copy=cut('pcl_ros.src','void toPCL(const sensor_msgs::PointCloud2 &pc2, pcl::PCLPointCloud2 &pcl_pc2)','\n  }')
conv=cut('pcl_conv.src','template <typename PointT> void\n  fromPCLPointCloud2 (const pcl::PCLPointCloud2& msg, pcl::PointCloud<PointT>& cloud,\n              const MsgFieldMap& field_map)', '\n  }')
flt=cut('filter.src','template <typename PointT> void\npcl::removeNaNFromPointCloud')
box=cut('bounds.src','template <typename PointT> inline void\npcl::getMinMax3D (const pcl::PointCloud<PointT> &cloud, Eigen::Vector4f &min_pt, Eigen::Vector4f &max_pt)')
assert 'specifies if all the data in <b>points</b> is finite' in P('pcl_cloud.src').read_text()
P('converted.inc').write_text(r+'\nnamespace pcl_conversions {\n'+meta+'\n'+copy+'\n}\nnamespace pcl {\n'+conv+'\n}\n'+flt+'\n'+box+'\n')
