"""Replacement publish_fast for six-barrier prospective-capacity evidence.

The compiler composes this ordinary source function with unchanged PROGRAM.
No run-time macro or source-level callback is introduced.
"""

def publish_fast():
    # Six actual barrier heads per conduit: two parallel paths of three
    # series members. I6 globalmax, I7/I8 triplet min/max, I9 path sum.
    # Query work may change I0..I5; these four retained slots are separate.
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
            else:
                # Missing or invalid raw data is worst capacity, not zero.
                source_iconstant(1, cap)
            if member % 6 == 0:
                source_iconstant(9, 0)
            if member % 3 == 0:
                source_icopy(7, 1)
                source_icopy(8, 1)
            elif member % 3 == 1:
                if source_ilt_register(1, 7):
                    source_icopy(7, 1)
                if source_ilt_register(8, 1):
                    source_icopy(8, 1)
            else:
                if source_ilt_register(1, 7):
                    source_icopy(1, 7)
                elif source_ilt_register(8, 1):
                    source_icopy(1, 8)
                source_iadd(9, 9, 1)
                if member % 6 == 5:
                    if not source_ilt(9, cap + 1):
                        source_iconstant(9, cap)
                    if source_ilt_register(6, 9):
                        source_icopy(6, 9)
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
