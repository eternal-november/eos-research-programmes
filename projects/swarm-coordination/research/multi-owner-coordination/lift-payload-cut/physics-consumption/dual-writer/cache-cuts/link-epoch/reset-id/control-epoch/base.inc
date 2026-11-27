#include <algorithm>
#include <cassert>
#include <cstdint>
#include <functional>
#include <iostream>
#include <limits>
#include <map>
#include <memory>
#include <mutex>
#include <set>
#include <sstream>
#include <string>
#include <unordered_map>
#include <vector>
#define GZ_PROFILE(...) ((void)0)
static std::ostringstream gzwarn;
using Entity=uint64_t;
using ComponentTypeId=int;
struct Vertex {
  Entity id{};
  auto Id()const{return id;}
  auto Data()const{return id;}
  bool Valid()const{return id!=0;}
};
struct EntityGraph {
  std::map<Entity,Vertex> body;
  void AddVertex(std::string,Entity e,Entity id){assert(e==id&&body.emplace(e,Vertex{e}).second);}
  auto Vertices()const{
    std::map<Entity,std::reference_wrapper<const Vertex>> out;
    for(const auto& [e,v]:body)out.emplace(e,std::cref(v));
    return out;
  }
  Vertex VertexFromId(Entity e)const{auto i=body.find(e);return i==body.end()?Vertex{}:i->second;}
  void RemoveVertex(Entity e){assert(body.erase(e)==1);}
};
namespace components {
struct BaseComponent {
  std::unique_ptr<BaseComponent> Clone()const {return std::make_unique<BaseComponent>();}
};
}
struct EntityComponentManagerDiff {
  std::set<Entity> added,removed;
  void InsertAddedEntity(Entity e){added.insert(e);}
  void InsertRemovedEntity(Entity e){removed.insert(e);}
  const auto& AddedEntities()const{return added;}
  const auto& RemovedEntities()const{return removed;}
};
struct EntityComponentManagerPrivate {
  // All nonempty storage and graph paths used below go through the extracted
  // operations. Native subsystem views and component payloads are unpopulated.
  EntityGraph entities;
  std::mutex entityCreatedMutex,entityRemoveMutex;
  uint64_t entityCount=0;
  bool removeAllEntities=false,lockAddEntitiesToViews=false,componentTypeIndexDirty=false;
  std::set<Entity> createdCompTypes,periodicChangedComponents,oneTimeChangedComponents,newlyCreatedEntities,toRemoveEntities,modifiedComponents;
  std::set<Entity> descendantCache,removedComponents,componentsMarkedAsRemoved,componentTypeIndexIterators,pinnedEntities;
  std::map<Entity,std::vector<std::unique_ptr<components::BaseComponent>>> componentStorage;
  std::map<Entity,std::unordered_map<ComponentTypeId,std::size_t>> componentTypeIndex;
  struct View { void RemoveEntity(Entity){assert(false);} };
  std::map<Entity,std::pair<View*,bool>> views;
  void CopyFrom(const EntityComponentManagerPrivate&);
  Entity CreateEntityImplementation(Entity);
};
struct EntityComponentManager {
  std::unique_ptr<EntityComponentManagerPrivate> dataPtr=std::make_unique<EntityComponentManagerPrivate>();
  Entity CreateEntity();
  void ProcessRemoveEntityRequests();
  void CopyFrom(const EntityComponentManager&);
  EntityComponentManagerDiff ComputeEntityDiff(const EntityComponentManager&)const;
  void ApplyEntityDiff(const EntityComponentManager&,const EntityComponentManagerDiff&);
  void ResetTo(const EntityComponentManager&);
  bool HasEntity(Entity e) const {return dataPtr->entities.VertexFromId(e).Valid();}
  // Selected graph-only single-remove request (no joint/query dependencies).
  void RequestRemoveEntity(Entity e,bool recurse){
    assert(!recurse&&dataPtr->views.empty()&&dataPtr->pinnedEntities.empty());
    dataPtr->toRemoveEntities.insert(e);
  }
  std::vector<ComponentTypeId> ComponentTypes(Entity) const {return {};}
  const components::BaseComponent* ComponentImplementation(Entity,ComponentTypeId) const{assert(false);return nullptr;}
  void CreateComponentImplementation(Entity,ComponentTypeId,const components::BaseComponent*){assert(false);}
};
/*PINNED*/

struct Report {std::string world;int era;Entity recipient;int job;bool prior_commit;};
bool legacy(const Report& msg,const Report& lookup){
  return msg.world==lookup.world&&msg.recipient==lookup.recipient&&msg.job==lookup.job&&msg.prior_commit;
}
bool scoped(const Report& msg,const Report& lookup){
  return msg.era==lookup.era&&legacy(msg,lookup);
}
int main(){
  int matched=0,reuse=0;
  for(Entity initial=0;initial<5;++initial)
  for(Entity extra=1;extra<=8;++extra)
  for(Entity keep=0;keep<(1u<<extra);++keep){
    EntityComponentManager p,init;
    for(Entity k=1;k<=initial;++k)assert(p.CreateEntity()==k);
    init.CopyFrom(p);
    for(Entity k=1;k<=extra;++k)assert(p.CreateEntity()==initial+k);
    Entity retained=initial;
    for(Entity i=0;i<extra;++i)
      if((keep>>i)&1)retained=initial+i+1;
      else p.RequestRemoveEntity(initial+i+1,false);
    p.ProcessRemoveEntityRequests();
    assert(p.dataPtr->entityCount==initial+extra); // no rewind on removal
    p.ResetTo(init);
    assert(p.dataPtr->entityCount==retained);
    for(Entity i=0;i<extra;++i)assert(p.HasEntity(initial+i+1)==bool((keep>>i)&1));
    p.ProcessRemoveEntityRequests();
    for(Entity i=0;i<extra;++i)assert(!p.HasEntity(initial+i+1));
    // Reuse each removed suffix ID, then issue a genuinely unused ID.
    for(Entity i=retained+1;i<=initial+extra+1;++i)
      assert(p.CreateEntity()==i);
    reuse+=retained<initial+extra;
    ++matched;
  }

  EntityComponentManager p,init;
  for(int i=0;i<10;++i)p.CreateEntity();
  init.CopyFrom(p);
  Entity prior=p.CreateEntity();
  const Report delayed{"same-world",1,prior,7,true};
  p.RequestRemoveEntity(prior,false);
  p.ProcessRemoveEntityRequests();
  assert(p.dataPtr->entityCount==prior&&!p.HasEntity(prior));
  p.ResetTo(init);
  p.ProcessRemoveEntityRequests();
  Entity replacement=p.CreateEntity();
  assert(prior==11&&replacement==prior);
  const Report current_unperformed{"same-world",2,replacement,7,false};
  assert(legacy(delayed,current_unperformed));
  assert(!scoped(delayed,current_unperformed));
  const Report current_earned{"same-world",2,replacement,7,true};
  assert(scoped(current_earned,current_unperformed));
  // If the original remains allocated, the reset difference protects this
  // one high-water mark, even though ResetTo schedules it for removal.
  p.ResetTo(init);
  p.ProcessRemoveEntityRequests();
  assert(p.CreateEntity()==replacement+1);
  // Re-sending a world ID, equal current simulation time, or storing the era
  // inside that same rewindable snapshot cannot by themselves prevent alias.
  const Report unsafe_rewind{"same-world",1,replacement,7,false};
  assert(scoped(delayed,unsafe_rewind));
  std::cout<<matched<<" ready/removed subset controls; "<<reuse<<" with a reused suffix after reset\n"
           <<"remove -> reset -> create reuses 11; scoped proof needs non-rewinding epoch\n"
           <<"retained high entity survives in the difference as a count bound\n";
}
