import Lean.Util.Reprove

namespace Array

reprove pmap_empty pmap_push attach_empty attachWith_empty map_map pmap_push attach_empty attachWith_empty by grind
reprove map_pmap pmap_map attach_push attachWith_push pmap_eq_map_attach pmap_eq_attachWith by grind
reprove attach_map_val attach_map_subtype_val attachWith_map_val attachWith_map_subtype_val by grind
reprove pmap_attach pmap_attachWith by grind
reprove attach_map attachWith_map map_attachWith map_attachWith_eq_pmap map_attach_eq_pmap by grind
reprove pmap_pmap pmap_append pmap_append' attach_append attachWith_append by grind
reprove pmap_reverse reverse_pmap attachWith_reverse reverse_attachWith attach_reverse reverse_attach by grind
reprove back?_pmap back?_attachWith back?_attach by grind

end Array

namespace Vector

reprove pmap_empty pmap_push attach_empty attachWith_empty map_map pmap_push attach_empty attachWith_empty by grind
reprove map_pmap pmap_map attach_push attachWith_push pmap_eq_map_attach pmap_eq_attachWith by grind
reprove attach_map_val attach_map_subtype_val attachWith_map_val attachWith_map_subtype_val by grind
reprove pmap_attach pmap_attachWith by grind
reprove attach_map attachWith_map map_attachWith map_attachWith_eq_pmap map_attach_eq_pmap by grind
reprove pmap_pmap pmap_append pmap_append' attach_append attachWith_append by grind
reprove pmap_reverse reverse_pmap attachWith_reverse reverse_attachWith attach_reverse reverse_attach by grind
reprove back?_pmap back?_attachWith back?_attach by grind

end Vector
