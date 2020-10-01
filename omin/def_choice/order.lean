import o_minimal.sheaf.yoneda
import o_minimal.order

namespace o_minimal

variables {R : Type*} [preorder R] {S : struc R} [is_definable_le S R]

lemma definable_Ioo : definable S (set.Ioo : R → R → set R) :=
begin [defin]
  intro a,
  intro b,
  intro x,
  app, app, exact definable.and.definable _,
  { app, app, exact (definable_iff_def_rel₂.mpr definable_lt').definable _,
    var, var },
  { app, app, exact (definable_iff_def_rel₂.mpr definable_lt').definable _,
    var, var }
end

lemma definable_Iio : definable S (set.Iio : R → set R) :=
begin [defin]
  intro b,
  intro x,
  app, app, exact (definable_iff_def_rel₂.mpr definable_lt').definable _,
  var, var
end

end o_minimal
