from pathlib import Path
import sys
def cut(path,start,stop=None):
    t=(Path(sys.argv[1])/path).read_text()
    t=t[t.index(start):]
    if stop: return t[:t.index(stop)]
    p=t.index('{')+1; deep=1
    while deep:
        deep+=(t[p]=='{')-(t[p]=='}');p+=1
    return t[:p]
pieces=[
('range.cc','rf_power log_normal_received_power','rf_power visibility_only_received_power'),
('table.cc','bool VisibilityTable::LoadLUT()',None),
('table.cc','VisibilityCost VisibilityTable::Cost(',None),
('model.cc','rf_power VisibilityModel::ComputeReceivedPower',None)]
Path('native.inc').write_text('namespace range_model {\n'+
    cut(*pieces[0])+'}\n'+'\n'.join(cut(*piece) for piece in pieces[1:]))
Path('mode.inc').write_text(cut('broker.cc','  // Build RF propagation function options',
    '  broker.SetDefaultRadioConfiguration'))
