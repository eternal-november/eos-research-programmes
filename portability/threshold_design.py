"""Explicit changed design point; historical production evidence stays separate."""
from dataclasses import replace
from fractions import Fraction as Q
import threshold_program_model as program

CLAMP_CUTOFF = Q(500000000)
CLAMP_LIMIT = 600000000
VECTOR_DRIVER_OFFSET = Q(30000000)
WARM_AT = 6800000000
EXTRA_REACTION = Q(324, 1000)


def design(isa):
    original = program.production_design(isa)
    physical = dict(original.physical_parameters)
    physical.update(CLAMP_LIMIT=CLAMP_LIMIT, WARM_AT=WARM_AT)
    return replace(original, physical_parameters=tuple(physical.items()))


def physical_parameters(compiled):
    c = compiled.constants
    return dict(clamp_cutoff=CLAMP_CUTOFF, clamp_limit=Q(c["CLAMP_LIMIT"]),
                power_at=Q(c["POWER_AT"]),
                vector_driver_at=Q(c["POWER_AT"])+VECTOR_DRIVER_OFFSET,
                vector_driver_offset=VECTOR_DRIVER_OFFSET,
                warm_at=Q(c["WARM_AT"]), extra_reaction=EXTRA_REACTION,
                field_extra_latency=Q(1,64), stroke_max=Q(11,10),
                stroke_lower_candidate=Q(1), cam_lower_candidate=Q(9,10),
                bank_clearance_candidate=Q(251658240),
                energy_clearance_candidate=Q(100),
                local_recognition_allocation=Q(50000),
                joint_source_realization=False)
