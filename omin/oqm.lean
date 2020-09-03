import algebra.module
import o_minimal.o_minimal
import o_minimal.algebra

open o_minimal

set_option old_structure_cmd true

class OQM (R : Type*) extends DUNLO R, ordered_add_comm_group R :=
[qmod : vector_space ℚ R]

attribute [instance] OQM.qmod

class o_minimal_add {R : Type*} [OQM R] (S : struc R) extends o_minimal S, is_definable_add S R

