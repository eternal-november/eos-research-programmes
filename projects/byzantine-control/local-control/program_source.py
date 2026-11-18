"""Finite imperative bank source. Compiled, never called by the runtime.

All arithmetic/control/array expressions elaborate to ordinary word instructions.
The named I/O calls below are single raw-location operations, not services.
"""

def main():
    boot()
    while 1:
        frame()

def boot():
    a = STACK_WORDS
    while a < DATA_WORDS:
        w[a] = 0
        a += 1
    w[ENTRY] = ENTRY_FRAMES
    w[PLANT_ENTRY] = PLANT_ENTRY_FRAMES
    t = 0
    while t < DEGREE:
        clear_target(TARGET_BASE + t * TARGET_WORDS)
        send_command(t, NEUTRAL_COMMAND)
        t += 1
    world(60, 60)
    source_invalidate()
    drain_start = cpu_count()
    drain = 0
    while (cpu_count() - drain_start) % COUNTER_MOD < BOOT_DRAIN_STEPS:
        drain += 1
    source_invalidate()

def count_fast(key, threshold):
    origin = 0
    count = 0
    while origin < ORIGINS:
        hit = fast_cmp(origin, 0, key, threshold)
        second = fast_cmp(origin, 1, key, threshold)
        hit = hit or second
        count += hit
        origin += 1
    return count

def count_range(key, lower, upper):
    origin = 0
    count = 0
    while origin < ORIGINS:
        hit = fast_range(origin, 0, key, lower, upper)
        second = fast_range(origin, 1, key, lower, upper)
        hit = hit or second
        count += hit
        origin += 1
    return count

def estimate(key, maximum):
    lo = 0
    hi = maximum
    while lo < hi:
        pivot = (lo + hi) // 2
        count = count_fast(key, pivot)
        if count >= QUORUM:
            hi = pivot
        else:
            lo = pivot + 1
    radius = POSE_VERIFY_RADIUS
    if key >= 3:
        relative = (key - 3) % FAST_TARGET_KEYS
        if relative == CAM:
            radius = CAM_VERIFY_RADIUS
        elif relative == CLAMP_A or relative == CLAMP_A + 1:
            radius = CLAMP_VERIFY_RADIUS
    if maximum == 2000:
        radius = ROW_VERIFY_RADIUS
    lower = lo - radius
    upper = lo + radius
    if lower < 0:
        lower = 0
    if upper > maximum:
        upper = maximum
    w[EST_VALID] = count_range(key, lower, upper) >= QUORUM
    return lo

def publish_value(key):
    client = 0
    while client < 2 * DEGREE:
        source_offer_fast(client, key)
        client += 1

def wait_conversion():
    polls = 0
    while polls < CONVERSION_POLLS and not source_ready():
        polls += 1
    return source_ready()

def publish_plant():
    key = 0
    while key < 3:
        source_start_fast(key)
        if wait_conversion() and source_ilt(1, 1 << SYMBOL_BITS):
            source_iadd_constant(1, 1, 0)
        else:
            source_iconstant(1, -1)
        publish_value(key)
        source_invalidate()
        key += 1

def publish_fast():
    # One visit samples one actual raw head. Functional maxima are ordinary
    # serialized folds; the I accumulator survives interleaved query work.
    visit = 0
    while visit < FAST_BATCH:
        raw = w[FAST_CURSOR]
        target = raw // RAW_TARGET_HEADS
        local = raw % RAW_TARGET_HEADS
        if local < VIEW_WORDS:
            key = 3 + target * FAST_TARGET_KEYS + local
            source_start_fast(key)
            if wait_conversion() and source_ilt(1, 1 << SYMBOL_BITS):
                source_iadd_constant(1, 1, 0)
                if local == MODE:
                    # One captured raw word:2*ACTIVE+FULL_LATCH.
                    if source_ieq(1, 2):
                        source_iconstant(1, 1)
                    elif source_ieq(1, 0) or source_ieq(1, 3):
                        source_iconstant(1, 0)
                    else:
                        source_iconstant(1, -1)
                elif local >= POSE_WORDS and not source_ilt(1, 2):
                    source_iconstant(1, -1)
            else:
                source_iconstant(1, -1)
            publish_value(key)
        else:
            member = local - VIEW_WORDS
            if member < CONNECTORS_A:
                side = 0
                kind = 0
                group = 0
                count = CONNECTORS_A
            elif member < CONNECTORS_A + CONNECTORS_B:
                member -= CONNECTORS_A
                side = 1
                kind = 0
                group = 1
                count = CONNECTORS_B
            elif member < 2 * CONNECTORS_A + CONNECTORS_B:
                member -= CONNECTORS_A + CONNECTORS_B
                side = 0
                kind = 1
                group = 2
                count = CONNECTORS_A
            else:
                member -= 2 * CONNECTORS_A + CONNECTORS_B
                side = 1
                kind = 1
                group = 3
                count = CONNECTORS_B
            if member == 0:
                source_iconstant(6, 0)
                w[FOLD_FAILED] = 0
            source_start_functional(target, side, member, kind)
            cap = LOAD_SENSOR_CAP
            if kind == 1:
                cap = 1000
            ready = wait_conversion()
            numeric = ready and source_ilt(1, SENSE_BIAS + cap + SENSE_ERROR + 1) and not source_ilt(1, SENSE_BIAS - SENSE_ERROR)
            if numeric:
                if source_ilt(1, SENSE_BIAS):
                    source_iconstant(1, 0)
                else:
                    source_iadd_constant(1, 1, -SENSE_BIAS)
                source_iadd_constant(1, 1, 0)
                if not source_ilt(1, cap + 1):
                    source_iconstant(1, cap)
                if kind == 1:
                    source_isub_constant(1, 1000, 1)
                if source_ilt_register(6, 1):
                    source_icopy(6, 1)
            else:
                w[FOLD_FAILED] = 1
            if member + 1 == count:
                key = 3 + target * FAST_TARGET_KEYS + VIEW_WORDS + group
                if w[FOLD_FAILED]:
                    source_iconstant(1, -1)
                else:
                    source_icopy(1, 6)
                publish_value(key)
        source_invalidate()
        w[FAST_CURSOR] = (raw + 1) % RAW_MAINT_HEADS
        visit += 1

def publish_queries():
    visit = 0
    while visit < QUERY_BATCH:
        slot = w[QUERY_CURSOR]
        client = slot // DEGREE
        target = slot % DEGREE
        source_capture_request(client, target)
        if source_ilt(0, CODE_KEYS):
            source_idiv(2, 0, BAYS * IMAGE_CELLS)
            source_idiv(3, 0, IMAGE_CELLS)
            source_imod(3, 3, BAYS)
            source_imod(4, 0, IMAGE_CELLS)
            source_start_cell(target)
            polls = 0
            while polls < CONVERSION_POLLS and not source_ready():
                polls += 1
            if source_ready() and source_ilt(1, 1 << SYMBOL_BITS):
                source_ishl(5, 0, SYMBOL_BITS)
                source_iadd(5, 5, 1)
                source_offer_reply(client, target)
            else:
                source_offer_missing(client, target)
        else:
            source_offer_missing(client, target)
        source_invalidate()
        w[QUERY_CURSOR] = (slot + 1) % (2 * DEGREE * DEGREE)
        visit += 1

def cell_result(t, side, bay, address):
    base = TARGET_BASE + t * TARGET_WORDS
    key = (side * BAYS + bay) * IMAGE_CELLS + address
    if not w[base + PENDING] or w[base + CELL_KEY] != key:
        origin = 0
        while origin < ORIGINS:
            request(origin, 0, t, key)
            request(origin, 1, t, key)
            origin += 1
        w[base + CELL_KEY] = key
        w[base + CELL_WAIT] = READ_WAIT_FRAMES
        w[base + PENDING] = 1
        return 0
    if w[base + CELL_WAIT] > 0:
        return 0
    expected = code[address]
    encoded = (key << SYMBOL_BITS) + expected
    origin = 0
    count = 0
    while origin < ORIGINS:
        hit = reply_equal(origin, 0, t, encoded)
        second = reply_equal(origin, 1, t, encoded)
        hit = hit or second
        count += hit
        origin += 1
    w[base + PENDING] = 0
    if count >= QUORUM:
        return 2
    return 1

def read_view(t):
    base = TARGET_BASE + t * TARGET_WORDS
    k = 0
    w[base + VIEW_VALID] = 1
    while k < POSE_WORDS:
        w[base + VIEW + k] = estimate(3 + t * FAST_TARGET_KEYS + k, POSE_MAX)
        if k == CAM:
            w[base + CAM_VALID] = w[EST_VALID]
        if k == CLAMP_A or k == CLAMP_A + 1:
            w[base + CLAMP_VALID_A + k - CLAMP_A] = w[EST_VALID]
        if not w[EST_VALID]:
            w[base + VIEW_VALID] = 0
        k += 1

def permission(base, side):
    if LOAD_MARGIN > 1000 or ISOLATION_MARGIN > 200:
        return 0
    target = (base - TARGET_BASE) // TARGET_WORDS
    key = 3 + target * FAST_TARGET_KEYS + VIEW_WORDS
    # Maxima are computed by renewed source code from EVERY actual connector.
    # Their oldest-member age and compare-to-withdrawal interval enter margins.
    load = count_fast(key + side, 1000 - LOAD_MARGIN)
    gap = count_fast(key + 2 + side, 200 - ISOLATION_MARGIN)
    return load >= QUORUM and gap >= QUORUM

def contact(t, relative):
    key = 3 + t * FAST_TARGET_KEYS + relative
    origin = 0
    count = 0
    while origin < ORIGINS:
        hit = fast_equal(origin, 0, key, 1)
        second = fast_equal(origin, 1, key, 1)
        hit = hit or second
        count += hit
        origin += 1
    return count >= QUORUM


def clear_target(base):
    w[base + CURSOR] = 0
    w[base + COMPLETED] = 0
    w[base + JOINED] = 0
    w[base + SCAN_BAY] = 0
    w[base + SCAN_ADDRESS] = 0
    w[base + SCAN_MATCH] = 1
    w[base + SELECTED] = 0
    w[base + VERIFY_ADDRESS] = 0
    w[base + PENDING] = 0
    j = 0
    while j < BAYS:
        w[base + ACCEPTED + j] = 0
        j += 1

def progress(base, half, phase, offset):
    cold = 1 - half
    v = base + VIEW
    if phase == 1:
        result = 0
        j = 0
        while j < BAYS:
            result += WARM_AT - w[v + ACT_A + cold * BAYS + j]
            j += 1
    elif phase == 2:
        result = CLAMP_LIMIT - w[v + CLAMP_A + cold]
    elif phase == 3:
        result = RESET_LIMIT - w[v + RESET_A + cold]
    elif phase == 4:
        result = w[v + RESET_A + cold]
    elif phase == 5:
        result = 0
        j = 0
        while j < BAYS:
            result += w[v + SEAT_A + cold * BAYS + j]
            j += 1
    elif phase == 6:
        result = w[v + CLAMP_A + cold]
    elif phase == 7:
        result = CUT_LIMIT - w[v + CUT_A + cold] + w[v + SHUNT_DEF_A + cold]
    elif phase == 8:
        result = 0
        j = 0
        while j < BAYS:
            result += w[v + ACT_A + cold * BAYS + j]
            j += 1
    elif phase == 9:
        if cold:
            result = w[v + BLEND]
        else:
            result = BLEND_LIMIT - w[v + BLEND]
    elif phase == 10 or phase == 0:
        side = cold
        if phase == 10:
            side = half
        result = 2000 - w[v + ISO_DEF_A + side] - w[v + SHUNT_DEF_A + side] + w[v + CUT_A + side]
        target = (base - TARGET_BASE) // TARGET_WORDS
        if contact(target, CUT_OPEN_A + side):
            result += RESERVE_CAP - w[v + ENERGY_A + side]
    elif phase == 11:
        result = w[v + ISO_DEF_A + cold]
    else:
        result = 0
    return result + 10 * offset

def first_activation(base, side, threshold):
    target = (base - TARGET_BASE) // TARGET_WORDS
    j = 0
    while j < BAYS:
        if threshold == 0:
            if not contact(target, ACT_ZERO_A + side * BAYS + j):
                return j + 1
        elif contact(target, ACT_POWER_A + side * BAYS + j):
            return j + 1
        j += 1
    return 0

def abort_action(t, base):
    v = base + VIEW
    if contact(t, ANCHOR_IS_A):
        anchor = 0
    elif contact(t, ANCHOR_IS_B):
        anchor = 1
    else:
        emit(t, MODE_PORT, 0, 0, FORCE)
        return 0
    cold = 1 - anchor
    entry = anchor * PHASES * SEGMENT
    active = first_activation(base, cold, 0)
    ready = contact(t, BLEND_AT_A + anchor) and contact(t, CUT_OPEN_A + cold) and contact(t, POWER_OFF_A + cold) and active == 0 and contact(t, CLAMP_OPEN_A + cold) and contact(t, RESET_OPEN_A + cold)
    if ready and contact(t, CAM_ENTRY_A + anchor):
        w[base + ABORT] = 0
        w[base + TIMER] = 0
        w[base + WATCH_HALF] = 0
        w[base + EXITING_ABORT] = 1
        w[base + EXIT_OBSERVED] = 0
        w[base + EXIT_WAIT] = 0
        clear_target(base)
        emit(t, MODE_PORT, cold, 0, -FORCE)
        return 0
    emit(t, MODE_PORT, cold, 0, FORCE)
    if not contact(t, BLEND_AT_A + anchor):
        if anchor:
            emit(t, BLEND_PORT, cold, 0, FORCE)
        else:
            emit(t, BLEND_PORT, cold, 0, -FORCE)
    elif not contact(t, ISO_SEATED_A + cold):
        emit(t, ISO_PORT, cold, 0, FORCE)
    elif not contact(t, SHUNT_SEATED_A + cold):
        emit(t, SHUNT_PORT, cold, 0, FORCE)
    elif not contact(t, CUT_OPEN_A + cold):
        if permission(base, cold):
            emit(t, CUT_PORT, cold, 0, FORCE)
    elif not contact(t, POWER_OFF_A + cold):
        pass
    elif active:
        emit(t, ACT_PORT, cold, active - 1, -FORCE)
    elif not contact(t, CLAMP_OPEN_A + cold):
        emit(t, CLAMP_PORT, cold, 0, -FORCE)
    elif not contact(t, RESET_OPEN_A + cold):
        emit(t, RESET_PORT, cold, 0, -FORCE)
    else:
        emit(t, REWIND_PORT, cold, 0, FORCE)
    return 0

def emit(t, port, side, index, amplitude):
    base = TARGET_BASE + t * TARGET_WORDS
    if port == MODE_PORT:
        w[base + CMD_MODE] = amplitude
    elif port == CAM_PORT:
        w[base + CMD_CAM] = amplitude
    else:
        w[base + CMD_ACTION] = port
        w[base + CMD_SIDE] = side
        w[base + CMD_INDEX] = index
        w[base + CMD_AMPLITUDE] = amplitude

def flush(t):
    base = TARGET_BASE + t * TARGET_WORDS
    record = w[base + CMD_ROUTE] + 32 * w[base + CMD_SIDE]
    record += 64 * (w[base + CMD_CAM] + 32)
    record += 4096 * (w[base + CMD_MODE] + 32)
    record += 262144 * w[base + CMD_ACTION]
    record += 4194304 * w[base + CMD_INDEX]
    record += (1 << 40) * (w[base + CMD_AMPLITUDE] + 32)
    send_command(t, record)

def exiting_abort(t, base):
    w[base + CMD_ROUTE] = 26
    w[base + CMD_SIDE] = 0
    emit(t, MODE_PORT, 0, 0, -FORCE)
    if contact(t, NORMAL_STOP):
        if not w[base + EXIT_OBSERVED]:
            w[base + EXIT_OBSERVED] = 1
            w[base + EXIT_WAIT] = POST_STAGE_FRAMES
        elif w[base + EXIT_WAIT] == 0:
            w[base + EXITING_ABORT] = 0
            w[base + EXIT_OBSERVED] = 0
            w[base + ABORT] = 0
            w[base + WATCH_HALF] = 0
            w[base + STAGE_ID] = 0
            w[base + RANK_VALID] = 0
            clear_target(base)
    else:
        w[base + EXIT_OBSERVED] = 0
        w[base + EXIT_WAIT] = 0

def helper(t):
    base = TARGET_BASE + t * TARGET_WORDS
    read_view(t)
    v = base + VIEW
    cam = w[v + CAM] % (2 * PHASES * SEGMENT)
    block = cam // SEGMENT
    half = block // PHASES
    phase = block % PHASES
    offset = cam % SEGMENT
    cold = 1 - half
    # Construct private desired fields; the previously applied record persists.
    # Only flush sends a bounded ordinary command record to the physical latch.
    p = CMD_ROUTE
    while p <= CMD_AMPLITUDE:
        w[base + p] = 0
        p += 1
    w[base + CMD_ROUTE] = half * PHASES + phase
    w[base + CMD_SIDE] = cold
    if w[base + EXITING_ABORT]:
        exiting_abort(t, base)
        flush(t)
        return 0
    if contact(t, ABORT_FULL):
        w[base + CMD_ROUTE] = 26
        if w[base + STAGE_ID] != 27:
            w[base + STAGE_ID] = 27
            w[base + STAGE_WAIT] = POST_STAGE_FRAMES
            w[base + PENDING] = 0
        if w[base + STAGE_WAIT] > 0:
            flush(t)
            return 0
        abort_action(t, base)
        action = w[base + CMD_ACTION]
        if action == 0 or w[base + CMD_MODE] < 0:
            w[base + ABORT_SIGNATURE] = 0
            w[base + ABORT_WAIT] = 0
        else:
            signature = action + PORTS * (w[base + CMD_SIDE] + 2 * w[base + CMD_INDEX])
            if signature != w[base + ABORT_SIGNATURE]:
                w[base + ABORT_SIGNATURE] = signature
                w[base + ABORT_WAIT] = POST_STAGE_FRAMES
            if w[base + ABORT_WAIT] > 0:
                w[base + CMD_ACTION] = 0
                w[base + CMD_AMPLITUDE] = 0
        flush(t)
        return 0
    if contact(t, MODE):
        # Genuine ENTERING sample cannot survive completed return under the
        # one-way/full-latch/travel contract; no negative absence inference.
        w[base + CMD_ROUTE] = 26
        emit(t, MODE_PORT, cold, 0, FORCE)
        flush(t)
        return 0
    if not w[base + CAM_VALID]:
        if w[base + WATCH_HALF] == 0:
            w[base + WATCH_HALF] = 3
            w[base + TIMER] = WATCH_FRAMES
        if w[base + TIMER] == 0:
            emit(t, MODE_PORT, cold, 0, FORCE)
        emit(t, CAM_PORT, cold, 0, FORCE)
        flush(t)
        return 0
    emit(t, CAM_PORT, cold, 0, FORCE)
    if offset < CAM_ERROR or offset + CAM_ERROR >= SEGMENT:
        if w[base + WATCH_HALF] == 0:
            w[base + WATCH_HALF] = 3
            w[base + TIMER] = WATCH_FRAMES
        if w[base + TIMER] == 0:
            emit(t, MODE_PORT, cold, 0, FORCE)
        flush(t)
        return 0
    stage = half * PHASES + phase + 1
    if w[base + STAGE_ID] != stage:
        w[base + STAGE_ID] = stage
        w[base + STAGE_WAIT] = POST_STAGE_FRAMES
        w[base + PENDING] = 0
    if w[base + STAGE_WAIT] > 0:
        flush(t)
        return 0
    rank = progress(base, half, phase, offset)
    if phase == 4:
        clear_target(base)
        w[base + ABORT] = 0
        w[base + TIMER] = WATCH_FRAMES
        w[base + WATCH_HALF] = half + 1
        w[base + LAST_PHASE] = phase
        w[base + HIGH] = rank + PROGRESS_ERROR
        w[base + RANK_VALID] = w[base + VIEW_VALID]
    elif w[base + WATCH_HALF] != half + 1 or phase > w[base + LAST_PHASE]:
        w[base + WATCH_HALF] = half + 1
        w[base + LAST_PHASE] = phase
        w[base + HIGH] = rank + PROGRESS_ERROR
        w[base + TIMER] = WATCH_FRAMES
        w[base + RANK_VALID] = w[base + VIEW_VALID]
        w[base + PENDING] = 0
    elif phase == w[base + LAST_PHASE] and w[base + VIEW_VALID]:
        if not w[base + RANK_VALID]:
            w[base + RANK_VALID] = 1
            w[base + HIGH] = rank + PROGRESS_ERROR
            w[base + TIMER] = WATCH_FRAMES
        elif rank - PROGRESS_ERROR > w[base + HIGH] + HIGH_STEP:
            w[base + HIGH] = rank + PROGRESS_ERROR
            w[base + TIMER] = WATCH_FRAMES
    if w[base + TIMER] == 0:
        w[base + ABORT] = 1
    if w[base + ABORT]:
        emit(t, MODE_PORT, cold, 0, FORCE)
        flush(t)
        return 0
    emit(t, CAM_PORT, cold, 0, FORCE)
    if phase == 0 or phase == 10:
        side = cold
        if phase == 10:
            side = half
        if not contact(t, ISO_SEATED_A + side):
            emit(t, ISO_PORT, side, 0, FORCE)
        elif not contact(t, SHUNT_SEATED_A + side):
            emit(t, SHUNT_PORT, side, 0, FORCE)
        elif permission(base, side):
            emit(t, CUT_PORT, side, 0, FORCE)
    elif phase == 1:
        active = first_activation(base, cold, 0)
        if active:
            emit(t, ACT_PORT, cold, active - 1, -FORCE)
    elif phase == 2:
        emit(t, CLAMP_PORT, cold, 0, -FORCE)
    elif phase == 3:
        emit(t, RESET_PORT, cold, 0, -FORCE)
    elif phase == 4:
        emit(t, RESET_PORT, cold, 0, FORCE)
    elif phase == 5:
        emit(t, INSERT_PORT, cold, 0, FORCE)
    elif phase == 6:
        if w[base + CLAMP_VALID_A + cold] and w[v + CLAMP_A + cold] - JOIN_ERROR >= JOIN_MARK:
            w[base + JOINED] = 1
        if not w[base + COMPLETED] and not w[base + JOINED]:
            address = w[base + CURSOR]
            if address < IMAGE_CELLS:
                if own_equal(t, cold, address, code[address]):
                    w[base + CURSOR] = address + 1
                else:
                    write_own(t, cold, address, code[address])
            w[base + COMPLETED] = w[base + CURSOR] == IMAGE_CELLS
        if w[base + COMPLETED] or w[base + JOINED]:
            emit(t, CLAMP_PORT, cold, 0, FORCE)
    elif phase == 7:
        if not contact(t, SHUNT_OPEN_A + cold):
            emit(t, SHUNT_PORT, cold, 0, -FORCE)
        else:
            emit(t, CUT_PORT, cold, 0, -FORCE)
    elif phase == 8:
        if w[base + SCAN_BAY] >= BAYS:
            w[base + SCAN_BAY] = 0
            w[base + SCAN_ADDRESS] = 0
            w[base + SCAN_MATCH] = 1
            j = 0
            while j < BAYS:
                w[base + ACCEPTED + j] = 0
                j += 1
        j = w[base + SCAN_BAY]
        address = w[base + SCAN_ADDRESS]
        result = cell_result(t, cold, j, address)
        if result:
            if result == 1:
                w[base + SCAN_MATCH] = 0
            w[base + SCAN_ADDRESS] = address + 1
            if w[base + SCAN_ADDRESS] == IMAGE_CELLS:
                w[base + ACCEPTED + j] = w[base + SCAN_MATCH]
                w[base + SCAN_BAY] = j + 1
                w[base + SCAN_ADDRESS] = 0
                w[base + SCAN_MATCH] = 1
            if w[base + SCAN_BAY] == BAYS:
                selected = 0
                j = 0
                while j < BAYS:
                    if selected == 0 and w[base + ACCEPTED + j]:
                        selected = j + 1
                    j += 1
                if selected == 0 or w[base + SELECTED] != 0 and selected != w[base + SELECTED]:
                    w[base + ABORT] = 1
                w[base + SELECTED] = selected
        if w[base + SELECTED]:
            emit(t, ACT_PORT, cold, w[base + SELECTED] - 1, FORCE)
    elif phase == 9:
        if cold:
            emit(t, BLEND_PORT, cold, 0, FORCE)
        else:
            emit(t, BLEND_PORT, cold, 0, -FORCE)
    elif phase == 11:
        emit(t, ISO_PORT, cold, 0, -FORCE)
    if phase == 9 or phase == 10:
        active = first_activation(base, cold, POWER_AT - 1)
        if active:
            address = w[base + VERIFY_ADDRESS]
            result = cell_result(t, cold, active - 1, address)
            if result:
                if result == 1:
                    w[base + ABORT] = 1
                w[base + VERIFY_ADDRESS] = (address + 1) % IMAGE_CELLS
    if w[base + ABORT]:
        emit(t, MODE_PORT, cold, 0, FORCE)
    flush(t)
    return 0

def frame():
    frame_start = cpu_count()
    publish_plant()
    publish_fast()
    publish_queries()
    if w[PLANT_ENTRY] > 0:
        w[PLANT_ENTRY] -= 1
        world(60, 60)
    else:
        sumrow = estimate(0, 2000)
        valid_sum = w[EST_VALID]
        diffrow = estimate(1, 2000) - 1000
        valid_diff = w[EST_VALID]
        x = (sumrow + diffrow) // 2
        y = (sumrow - diffrow) // 2
        ux = 60 + (2 * (x - 500)) // 10
        uy = 60 + (2 * (y - 500)) // 10
        if ux < 30:
            ux = 30
        if ux > 90:
            ux = 90
        if uy < 30:
            uy = 30
        if uy > 90:
            uy = 90
        if valid_sum and valid_diff:
            world(ux, uy)
        else:
            world(60, 60)
    if w[ENTRY] > 0:
        w[ENTRY] -= 1
    else:
        visits = 0
        while visits < MAINT_BATCH:
            target = w[MAINT_CURSOR]
            helper(target)
            w[MAINT_CURSOR] = (target + 1) % DEGREE
            visits += 1
    target = 0
    while target < DEGREE:
        base = TARGET_BASE + target * TARGET_WORDS
        if w[base + TIMER] > 0:
            w[base + TIMER] -= 1
        if w[base + CELL_WAIT] > 0:
            w[base + CELL_WAIT] -= 1
        if w[base + STAGE_WAIT] > 0:
            w[base + STAGE_WAIT] -= 1
        if w[base + ABORT_WAIT] > 0:
            w[base + ABORT_WAIT] -= 1
        if w[base + EXIT_WAIT] > 0:
            w[base + EXIT_WAIT] -= 1
        target += 1
    padding = 0
    while (cpu_count() - frame_start) % COUNTER_MOD < FRAME_STEPS:
        padding += 1
    yield_frame()
