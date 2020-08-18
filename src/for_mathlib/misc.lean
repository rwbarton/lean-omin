lemma subsingleton_injective {α β : Sort*} [subsingleton α] (f : α → β) :
  function.injective f :=
by { intros _ _, cc }
