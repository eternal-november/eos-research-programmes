#include <algorithm>
#include <cassert>
#include <cmath>
#include <iostream>
#include <map>
#include <optional>
#include <utility>
#include <vector>
#define ROS_INFO_COND(...) do{}while(0)
#define ROS_WARN_COND(...) do{}while(0)
namespace octomap {
struct point3d {
    float x,y,z;
    point3d operator-(const point3d& b)const{return {x-b.x,y-b.y,z-b.z};}
    float norm_sq()const{return x*x+y*y+z*z;}
    float norm()const{return std::sqrt(norm_sq());}
};
using OcTreeKey=int;
struct NodeData {point3d pos; float radius; unsigned segment_id; int k;};
struct Node {
    NodeData data;
    NodeData* valuePtr(){return &data;}
};
struct SphereMapOcTree{
    std::vector<Node> values;
    point3d focus; float h;
    Node* search(int k){return &values.at(k);}
    class leaf_bbx_iterator{
        SphereMapOcTree* t; size_t idx;
        void step(){
            while(idx<t->values.size()) {
                const auto v=t->values[idx].data.pos - t->focus;
                if(std::abs(v.x)<=t->h && std::abs(v.y)<=t->h && std::abs(v.z)<=t->h)return;
                ++idx;
            }
        }
    public:
        leaf_bbx_iterator(SphereMapOcTree* a,size_t i):t(a),idx(i){step();}
        bool operator!=(const leaf_bbx_iterator& a)const{return idx!=a.idx;}
        leaf_bbx_iterator& operator++(){++idx;step();return *this;}
        leaf_bbx_iterator operator++(int){auto old=*this; ++*this; return old;}
        Node* operator->(){return &t->values[idx];}
        int getKey()const{return t->values[idx].data.k;}
    };
    leaf_bbx_iterator begin_leafs_bbx(int,int){return {this,0};}
    leaf_bbx_iterator end_leafs_bbx(){return {this,values.size()};}
};
}
struct SphereMapPath{
    bool reaches_goal=false;
    std::vector<octomap::point3d> positions;
    std::vector<float> obstacle_dists;
};
struct SphereMap{
    octomap::SphereMapOcTree tree;
    octomap::SphereMapOcTree* nodes=&tree;
    float enforced_max_sphere_radius=3;
    float planning_min_safe_dist=0;
    std::map<uint,int> segments{{1,0}};
    std::pair<octomap::OcTreeKey,octomap::OcTreeKey> getMaxSearchBBXBorderKeys(octomap::point3d p,float h){
        tree.focus=p;tree.h=h;return {0,0};
    }
    bool areConnectable(float d2,float r,float g){return d2<(r+g)*(r+g);}
    std::optional<std::pair<float,octomap::OcTreeKey>> getNearestNodeKey(octomap::point3d,float);
    std::vector<std::pair<float,octomap::OcTreeKey>> getNearestNodeKeysForEachSegment(octomap::point3d,float,bool=false,float=0);
    std::optional<std::vector<SphereMapPath>> computePathsToGoalsWithConnectingToGraph(
        octomap::point3d,float,std::vector<octomap::point3d>,float,bool,bool);
    // Supplied graph route; its existence is held fixed. No stock A*
    // implementation or 3D occupancy update is executed by this fixture.
    SphereMapPath graph_path(int a,int b){
        auto x=nodes->search(a)->data,y=nodes->search(b)->data;
        const auto overlay=x.pos-y.pos;
        if(!(overlay.norm() < x.radius + y.radius))return {};
        return {true,{x.pos,y.pos},{x.radius,y.radius}};
    }
    SphereMapPath computePath(uint,octomap::point3d,uint,octomap::point3d,bool,int a,int b,bool){
        return graph_path(a,b);
    }
    SphereMapPath computeDetailedPathInSegment(int a,int b,std::map<uint,int>::iterator,float,bool){
        return graph_path(a,b);
    }
};
#include "source.inc"
int main(){
    int n;
    while(std::cin>>n){
        SphereMap m;
        for(int i=0;i<n;++i){
            octomap::NodeData a;std::cin>>a.pos.x>>a.pos.y>>a.pos.z>>a.radius>>a.segment_id;
            a.k=i;m.tree.values.push_back({a});
        }
        octomap::point3d p,q;float mD;bool c;
        std::cin>>p.x>>p.y>>p.z>>q.x>>q.y>>q.z>>mD>>c;
        auto s=m.getNearestNodeKey(p,mD);
        auto g=m.getNearestNodeKeysForEachSegment(q,mD);
        auto r=m.computePathsToGoalsWithConnectingToGraph(p,mD,{q},mD,false,c);
        bool nonempty=r&&r->size()&&!r->at(0).positions.empty();
        std::cout.precision(10);
        std::cout<<(s?s->second:-1)<<' '<<(s?s->first:0)<<' '<<g.size()<<' '<<nonempty;
        if(nonempty){
            for(size_t i=0;i<r->at(0).positions.size();++i){
                auto t=r->at(0).positions[i];
                std::cout<<' '<<t.x<<' '<<t.y<<' '<<t.z<<' '<<r->at(0).obstacle_dists[i];
            }
        }
        std::cout<<'\n';
    }
}
