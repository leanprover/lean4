import Lean.Util.Reprove

namespace Array

reprove pmap_empty pmap_push attach_empty attachWith_empty by grind
reprove map_pmap pmap_map attach_push attachWith_push pmap_eq_map_attach pmap_eq_attachWith by grind
reprove attach_map_val attach_map_subtype_val attachWith_map_val attachWith_map_subtype_val by grind
reprove pmap_attach pmap_attachWith by grind
reprove attach_map attachWith_map map_attachWith map_attachWith_eq_pmap map_attach_eq_pmap by grind
reprove pmap_pmap pmap_append pmap_append' attach_append attachWith_append by grind
reprove pmap_reverse reverse_pmap attachWith_reverse reverse_attachWith attach_reverse reverse_attach by grind
reprove back?_pmap back?_attachWith back?_attach by grind

end Array

namespace Vector

reprove pmap_empty pmap_push attach_empty attachWith_empty by grind
reprove map_pmap pmap_map attach_push attachWith_push pmap_eq_map_attach pmap_eq_attachWith by grind
reprove attach_map_val attach_map_subtype_val attachWith_map_val attachWith_map_subtype_val by grind
reprove pmap_attach pmap_attachWith by grind
reprove attach_map attachWith_map map_attachWith map_attachWith_eq_pmap map_attach_eq_pmap by grind
reprove pmap_pmap pmap_append pmap_append' attach_append attachWith_append by grind
reprove pmap_reverse reverse_pmap attachWith_reverse reverse_attachWith attach_reverse reverse_attach by grind
reprove back?_pmap back?_attachWith back?_attach by grind

end Vector

namespace List

-- `grind` is less capable on List by default, because the theorems are set up to use induction and `cons`,
-- rathering than extensionality via indices. Here we just use extensionality.
attribute [local grind ←=] List.ext_getElem

reprove pmap_nil pmap_cons attach_nil attachWith_nil by grind
reprove map_pmap pmap_map attach_cons attachWith_cons pmap_eq_map_attach pmap_eq_attachWith by grind
reprove attach_map_val attach_map_subtype_val attachWith_map_val attachWith_map_subtype_val by grind
reprove pmap_attach pmap_attachWith by grind
reprove attach_map attachWith_map map_attachWith map_attachWith_eq_pmap map_attach_eq_pmap by grind
reprove pmap_pmap pmap_append pmap_append' attach_append attachWith_append by grind
reprove pmap_reverse reverse_pmap attachWith_reverse reverse_attachWith attach_reverse reverse_attach by grind
reprove getLast?_pmap getLast?_attachWith getLast?_attach by grind

end List

namespace Option

reprove pmap_none pmap_some attach_none attachWith_none by grind
reprove map_pmap pmap_map attach_some attachWith_some by grind
reprove attach_map_subtype_val attachWith_map_val attachWith_map_subtype_val by grind [cases Option]
reprove attach_map  attachWith_map map_attachWith by grind [cases Option]
reprove map_attachWith_eq_pmap map_attach_eq_pmap by grind [cases Option]

end Option
