"""Actual-target and origin-footprint checks for the local ring source."""
import argparse
from hashlib import sha256
from itertools import combinations
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
OFFSETS = tuple(range(-20, 0)) + tuple(range(1, 21))


def require(condition, message):
    if not condition:
        raise AssertionError(message)


def neighbors(i, n):
    return tuple((i+s) % n for s in OFFSETS)


def groups(i, target, n):
    target_neighbors = set(neighbors(target, n))
    candidates = tuple(j for j in neighbors(i, n) if j in target_neighbors)
    require(len(candidates) >= 19, "Not enough physically common observers")
    selected = candidates[:13]
    require(i not in selected and target not in selected and len(set(selected)) == 13,
            "Primary/receiver/target alias")
    return selected, len(candidates)


def reached_slots(receiver, selected, domains):
    out = set()
    if receiver in domains or selected[0] in domains:
        out.add(0)
    for slot, origin in enumerate(selected[1:], 1):
        if origin in domains:
            out.add(slot)
    return out


def ring_check(m, regions):
    n = m*regions
    require(m >= 72 and m % 2 == 0 and regions >= 6, "Outside declared family")
    rosters = [neighbors(i, n) for i in range(n)]
    inverse = [{target:index for index,target in enumerate(row)} for row in rosters]
    target_routes = plant_routes = 0
    minima = 40
    changed_ordinals = 0
    writer_leads = 0
    for receiver in range(n):
        for local_target, target in enumerate(rosters[receiver]):
            selected, size = groups(receiver, target, n)
            minima = min(minima, size)
            k = abs(OFFSETS[local_target])
            require(size == 39-k, "Intersection count mismatch")
            for origin in selected:
                provider_target = inverse[origin][target]
                require(rosters[origin][provider_target] == target, "Wrong provider object")
                # Return lane is bound to this receiver and same physical target.
                returned_target = inverse[receiver][rosters[origin][provider_target]]
                require(returned_target == local_target, "Return changed target")
                require(receiver in inverse[origin], "No direct client branch")
                for bank in (0, 1):
                    client_slot = 2 * inverse[origin][receiver] + bank
                    require(0 <= client_slot < 80 and client_slot % 2 == bank,
                            "Client bank identity was lost")
                changed_ordinals += int(provider_target != local_target)
                target_routes += 1
            # One domain has at most one logical effect, including frontend reach.
            for domain in (receiver, *selected):
                require(len(reached_slots(receiver, selected, {domain})) <= 1,
                        "A host domain reached multiple origin slots")
        for row_parity in (0, 1):
            candidates = [j for j in rosters[receiver] if j % 2 == row_parity]
            require(len(candidates) == 20, "Complementary row coverage changed")
            for origin in candidates[:13]:
                provider_region = origin // m
                wanted_region = receiver // m
                region_heads = ((provider_region-1) % regions, provider_region,
                                (provider_region+1) % regions)
                require(wanted_region in region_heads, "Plant target outside physical heads")
                head = region_heads.index(wanted_region)
                require(0 <= head < 3 and origin != receiver, "Invalid plant source")
                plant_routes += 1
    for target in range(n):
        owned = {}
        for producer in rosters[target]:
            for bank in (0, 1):
                bay = 2 * inverse[target][producer] + bank
                require(bay not in owned, "Two producer banks share a candidate write lead")
                owned[bay] = (producer, bank)
                writer_leads += 1
        require(set(owned) == set(range(80)), "Candidate layout is not a bijection")
    return dict(hosts=n, region_size=m, regions=regions, minimum_common_observers=minima,
                maintenance_target_routes=target_routes, plant_routes=plant_routes,
                routes_requiring_ordinal_translation=changed_ordinals,
                private_producer_bank_leads_per_prepared_side=writer_leads)


def correlation_checks():
    receiver, n = 0, 432
    cases = 0
    for target in neighbors(receiver, n):
        selected, _ = groups(receiver, target, n)
        domains = (receiver, *selected)
        for count in range(7):
            for subset in combinations(domains, count):
                require(len(reached_slots(receiver, selected, set(subset))) <= count,
                        "Joint source footprint exceeded its actual domains")
                cases += 1
    # Duplicating the primary backend creates two votes from one domain.
    selected, _ = groups(0, 1, n)
    duplicate = (selected[0], selected[0], *selected[2:])
    require(len(reached_slots(0, duplicate, {selected[0]})) == 2,
            "Duplicate-origin counterexample lost")
    # A common receiver remapper reaches all slots while execution is unchanged.
    require(len(set(range(13))) > 6, "Wide input counterexample lost")
    # Same integer ordinal does not preserve the physical target.
    receiver, target, provider = 0, 1, 2
    consumer_ordinal = neighbors(receiver, n).index(target)
    provider_ordinal = neighbors(provider, n).index(target)
    wrong_target = neighbors(provider, n)[consumer_ordinal]
    require((consumer_ordinal, provider_ordinal, wrong_target) == (20, 19, 3),
            "Actual-object mismatch witness changed")
    return dict(joint_domain_subset_checks=cases, duplicated_primary_backend_votes=2,
                common_remapper_can_reach_all_slots=True,
                local_ordinal_counterexample=dict(receiver=receiver, target=target,
                    provider=provider, consumer_ordinal=consumer_ordinal,
                    provider_ordinal=provider_ordinal, incorrect_same_ordinal_target=wrong_target))


def main():
    parser = argparse.ArgumentParser()
    mode = parser.add_mutually_exclusive_group(required=True)
    mode.add_argument('--write', action='store_true')
    mode.add_argument('--check', action='store_true')
    args = parser.parse_args()
    result = dict(status='constructed incidence adapter; physical source/PROGRAM integration and independent review pending',
                  sources={name:sha256((HERE/name).read_bytes().replace(b'\r\n', b'\n')).hexdigest()
                           for name in ('INCIDENCE.md', 'incidence_model.py')},
                  rings=[ring_check(*pair) for pair in ((72,6),(74,6),(72,7))],
                  correlation=correlation_checks())
    rendered = json.dumps(result, sort_keys=True, indent=2) + '\n'
    record = HERE/'incidence_results.json'
    if args.write:
        record.write_text(rendered, encoding='utf-8')
        print('incidence record written')
    else:
        require(record.read_text(encoding='utf-8') == rendered, 'Incidence record is stale')
        print('incidence record matches')


if __name__ == '__main__':
    main()
