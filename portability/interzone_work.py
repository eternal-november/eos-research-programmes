"""Sufficient ready-stock and recovery bounds for a receiver-local work parcel."""
from dataclasses import dataclass
from fractions import Fraction as Q

from constructors import exact, reservoir_margin


@dataclass(frozen=True)
class LocalWork:
    usable_at_charge_limit: Q
    ready_floor: Q
    refill_time: Q | None


def local_work(charge_limit, pending_max, burst, rate, net_input, latency):
    """The input service curve applies to every interval below the charge limit."""
    limit=exact(charge_limit,"charging threshold")
    pending=exact(pending_max,"maximum locally reserved stock")
    if not 0 <= pending < limit:
        raise ValueError("The charge threshold must include available energy")
    usable=limit-pending
    floor=reservoir_margin(usable,burst,rate,net_input,latency)
    # A positive surplus is needed for this repair guarantee from arbitrary depletion.
    recovery=None if net_input==rate else (usable+burst+net_input*latency)/(net_input-rate)
    return LocalWork(usable,floor,recovery)


def check_remote_order():
    import rx_product as rx

    def second_event(first_open):
        payer=rx.raw.SourceWork(2,32,32)
        lanes=[rx.raw.RawLane(82,rx.raw.LaneId(2,0,receiver,0),payer) for receiver in (0,1)]
        specs=rx.phases(lanes)
        clocks=[rx.Receiver(lane,specs[lane.identity]) for lane in lanes]
        lanes[0].write_gate=first_open
        for clock in clocks:
            clock.act(("base",None))
        return lanes[1].rx[rx.DIVIDER]

    assert second_event(False)==1 and second_event(True)==0
    hard_power=2**100+2**94
    assert Q(hard_power,2**110)<Q(1,512)<32
    assert Q(300**2,2**64)<Q(1,10**12)
    print("Same remote receiver view, scarce origin: distinct divider results 1 and 0")


def main():
    # Illustrative service curves, not a new physical rating of the old rail.
    rate=32*4096*Q(101,100)
    lag=Q(1,4096)
    witness=local_work(160,32,32,rate,2*rate,lag)
    assert witness.ready_floor==Q(1592,25) and witness.refill_time< Q(2,1000)
    assert local_work(160,32,32,rate,rate,lag).refill_time is None
    for bad in ((32,32,1,1,2,0),(65,32,32,1,2,1)):
        try: local_work(*bad)
        except ValueError: pass
        else: raise AssertionError("A promised parcel was counted as ready work")
    print(f"Conditional local floor {witness.ready_floor}; recharge bound {witness.refill_time}q")
    check_remote_order()


if __name__=="__main__":
    main()
