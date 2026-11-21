// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Context
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Basic public import Lean.Elab.Tactic.VCGen.SpecDB public import Lean.Elab.Tactic.VCGen.FrameProc public import Lean.Meta.Sym.Apply public import Lean.Meta.Sym.Simp.DiscrTree public import Lean.Elab.Tactic.VCGen.RIntroAttr public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Tactic.Grind.Types
#include <lean/lean.h>
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
#ifdef __cplusplus
extern "C" {
#endif
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default___redArg();
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_Meta_Sym_Simp_SimpM_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
extern lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_instInhabitedSpecTheorems_default;
extern lean_object* l_Lean_Meta_Sym_instInhabitedPattern_default;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__0;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "WP"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(193, 201, 27, 53, 82, 85, 158, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__2_value),LEAN_SCALAR_PTR_LITERAL(202, 119, 227, 254, 29, 206, 25, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 221, 47, 20, 208, 169, 53, 145)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_of_forall_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(101, 62, 242, 60, 214, 49, 44, 186)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "le_of_imp_top_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value),LEAN_SCALAR_PTR_LITERAL(93, 90, 131, 207, 158, 255, 244, 86)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ofProp_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__12_value),LEAN_SCALAR_PTR_LITERAL(106, 190, 25, 190, 179, 48, 235, 2)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ofProp_meet_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value),LEAN_SCALAR_PTR_LITERAL(239, 140, 127, 117, 148, 144, 166, 107)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__14_value),LEAN_SCALAR_PTR_LITERAL(218, 169, 77, 37, 89, 171, 140, 233)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "iSup_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__16_value),LEAN_SCALAR_PTR_LITERAL(199, 118, 246, 228, 14, 114, 190, 48)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "true_le_of_top_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__18_value),LEAN_SCALAR_PTR_LITERAL(246, 158, 62, 101, 253, 23, 66, 126)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "top_le_prop"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__20_value),LEAN_SCALAR_PTR_LITERAL(100, 220, 104, 174, 27, 127, 1, 211)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__22_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rel_refl"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__24_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__25_value),LEAN_SCALAR_PTR_LITERAL(114, 93, 162, 136, 122, 175, 235, 220)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "meet_top_le_of_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__27_value),LEAN_SCALAR_PTR_LITERAL(242, 230, 85, 150, 218, 12, 92, 28)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_forall"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__29_value),LEAN_SCALAR_PTR_LITERAL(57, 100, 144, 90, 138, 155, 244, 133)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "_inhabitedExprDummy"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 247, 56, 151, 29, 116, 116, 243)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__2;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__3;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint;
static const lean_array_object l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__0_value)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedJump = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_instInhabitedJump_default___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__0;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__1;
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_runSimp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__1(void){
_start:
{
uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_3_ = 0;
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_box(0);
v___x_6_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__0));
v___x_7_ = l_Lean_Meta_Sym_instInhabitedPattern_default;
v___x_8_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
lean_ctor_set(v___x_8_, 2, v___x_5_);
lean_ctor_set(v___x_8_, 3, v___x_4_);
lean_ctor_set_uint8(v___x_8_, sizeof(void*)*4, v___x_3_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__1, &l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default___closed__1);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default;
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__0(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Meta_DiscrTree_empty___redArg();
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__2(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__1));
v___x_15_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__0, &l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__0);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__2, &l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB___closed__2);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules(lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4));
v___x_94_ = lean_box(0);
v___x_95_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_93_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v_a_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v_a_96_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_a_96_);
lean_dec_ref_known(v___x_95_, 1);
v___x_97_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8));
v___x_98_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_97_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_98_) == 0)
{
lean_object* v_a_99_; lean_object* v___x_100_; lean_object* v___x_101_; 
v_a_99_ = lean_ctor_get(v___x_98_, 0);
lean_inc(v_a_99_);
lean_dec_ref_known(v___x_98_, 1);
v___x_100_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10));
v___x_101_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_100_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_101_) == 0)
{
lean_object* v_a_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v_a_102_ = lean_ctor_get(v___x_101_, 0);
lean_inc(v_a_102_);
lean_dec_ref_known(v___x_101_, 1);
v___x_103_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13));
v___x_104_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_103_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_104_) == 0)
{
lean_object* v_a_105_; lean_object* v___x_106_; lean_object* v___x_107_; 
v_a_105_ = lean_ctor_get(v___x_104_, 0);
lean_inc(v_a_105_);
lean_dec_ref_known(v___x_104_, 1);
v___x_106_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15));
v___x_107_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_106_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; lean_object* v___x_110_; 
v_a_108_ = lean_ctor_get(v___x_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v___x_107_, 1);
v___x_109_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17));
v___x_110_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_109_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_110_) == 0)
{
lean_object* v_a_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
v_a_111_ = lean_ctor_get(v___x_110_, 0);
lean_inc(v_a_111_);
lean_dec_ref_known(v___x_110_, 1);
v___x_112_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19));
v___x_113_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_112_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_113_) == 0)
{
lean_object* v_a_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_a_114_ = lean_ctor_get(v___x_113_, 0);
lean_inc(v_a_114_);
lean_dec_ref_known(v___x_113_, 1);
v___x_115_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21));
v___x_116_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_115_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_116_) == 0)
{
lean_object* v_a_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_a_117_ = lean_ctor_get(v___x_116_, 0);
lean_inc(v_a_117_);
lean_dec_ref_known(v___x_116_, 1);
v___x_118_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23));
v___x_119_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_118_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_119_) == 0)
{
lean_object* v_a_120_; lean_object* v___x_121_; lean_object* v___x_122_; 
v_a_120_ = lean_ctor_get(v___x_119_, 0);
lean_inc(v_a_120_);
lean_dec_ref_known(v___x_119_, 1);
v___x_121_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26));
v___x_122_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_121_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_122_) == 0)
{
lean_object* v_a_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v_a_123_ = lean_ctor_get(v___x_122_, 0);
lean_inc(v_a_123_);
lean_dec_ref_known(v___x_122_, 1);
v___x_124_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28));
v___x_125_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_124_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
v_a_126_ = lean_ctor_get(v___x_125_, 0);
lean_inc(v_a_126_);
lean_dec_ref_known(v___x_125_, 1);
v___x_127_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30));
v___x_128_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_127_, v___x_94_, v_a_88_, v_a_89_, v_a_90_, v_a_91_);
if (lean_obj_tag(v___x_128_) == 0)
{
lean_object* v_a_129_; lean_object* v___x_131_; uint8_t v_isShared_132_; uint8_t v_isSharedCheck_137_; 
v_a_129_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_137_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_137_ == 0)
{
v___x_131_ = v___x_128_;
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
else
{
lean_inc(v_a_129_);
lean_dec(v___x_128_);
v___x_131_ = lean_box(0);
v_isShared_132_ = v_isSharedCheck_137_;
goto v_resetjp_130_;
}
v_resetjp_130_:
{
lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_133_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_133_, 0, v_a_96_);
lean_ctor_set(v___x_133_, 1, v_a_99_);
lean_ctor_set(v___x_133_, 2, v_a_102_);
lean_ctor_set(v___x_133_, 3, v_a_105_);
lean_ctor_set(v___x_133_, 4, v_a_108_);
lean_ctor_set(v___x_133_, 5, v_a_111_);
lean_ctor_set(v___x_133_, 6, v_a_114_);
lean_ctor_set(v___x_133_, 7, v_a_117_);
lean_ctor_set(v___x_133_, 8, v_a_120_);
lean_ctor_set(v___x_133_, 9, v_a_123_);
lean_ctor_set(v___x_133_, 10, v_a_126_);
lean_ctor_set(v___x_133_, 11, v_a_129_);
if (v_isShared_132_ == 0)
{
lean_ctor_set(v___x_131_, 0, v___x_133_);
v___x_135_ = v___x_131_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
else
{
lean_object* v_a_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_145_; 
lean_dec(v_a_126_);
lean_dec(v_a_123_);
lean_dec(v_a_120_);
lean_dec(v_a_117_);
lean_dec(v_a_114_);
lean_dec(v_a_111_);
lean_dec(v_a_108_);
lean_dec(v_a_105_);
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_138_ = lean_ctor_get(v___x_128_, 0);
v_isSharedCheck_145_ = !lean_is_exclusive(v___x_128_);
if (v_isSharedCheck_145_ == 0)
{
v___x_140_ = v___x_128_;
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_a_138_);
lean_dec(v___x_128_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_145_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v___x_143_; 
if (v_isShared_141_ == 0)
{
v___x_143_ = v___x_140_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_144_; 
v_reuseFailAlloc_144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_144_, 0, v_a_138_);
v___x_143_ = v_reuseFailAlloc_144_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
return v___x_143_;
}
}
}
}
else
{
lean_object* v_a_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_153_; 
lean_dec(v_a_123_);
lean_dec(v_a_120_);
lean_dec(v_a_117_);
lean_dec(v_a_114_);
lean_dec(v_a_111_);
lean_dec(v_a_108_);
lean_dec(v_a_105_);
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_146_ = lean_ctor_get(v___x_125_, 0);
v_isSharedCheck_153_ = !lean_is_exclusive(v___x_125_);
if (v_isSharedCheck_153_ == 0)
{
v___x_148_ = v___x_125_;
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_a_146_);
lean_dec(v___x_125_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_153_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_151_; 
if (v_isShared_149_ == 0)
{
v___x_151_ = v___x_148_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v_a_146_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
else
{
lean_object* v_a_154_; lean_object* v___x_156_; uint8_t v_isShared_157_; uint8_t v_isSharedCheck_161_; 
lean_dec(v_a_120_);
lean_dec(v_a_117_);
lean_dec(v_a_114_);
lean_dec(v_a_111_);
lean_dec(v_a_108_);
lean_dec(v_a_105_);
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_154_ = lean_ctor_get(v___x_122_, 0);
v_isSharedCheck_161_ = !lean_is_exclusive(v___x_122_);
if (v_isSharedCheck_161_ == 0)
{
v___x_156_ = v___x_122_;
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
else
{
lean_inc(v_a_154_);
lean_dec(v___x_122_);
v___x_156_ = lean_box(0);
v_isShared_157_ = v_isSharedCheck_161_;
goto v_resetjp_155_;
}
v_resetjp_155_:
{
lean_object* v___x_159_; 
if (v_isShared_157_ == 0)
{
v___x_159_ = v___x_156_;
goto v_reusejp_158_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v_a_154_);
v___x_159_ = v_reuseFailAlloc_160_;
goto v_reusejp_158_;
}
v_reusejp_158_:
{
return v___x_159_;
}
}
}
}
else
{
lean_object* v_a_162_; lean_object* v___x_164_; uint8_t v_isShared_165_; uint8_t v_isSharedCheck_169_; 
lean_dec(v_a_117_);
lean_dec(v_a_114_);
lean_dec(v_a_111_);
lean_dec(v_a_108_);
lean_dec(v_a_105_);
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_162_ = lean_ctor_get(v___x_119_, 0);
v_isSharedCheck_169_ = !lean_is_exclusive(v___x_119_);
if (v_isSharedCheck_169_ == 0)
{
v___x_164_ = v___x_119_;
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
else
{
lean_inc(v_a_162_);
lean_dec(v___x_119_);
v___x_164_ = lean_box(0);
v_isShared_165_ = v_isSharedCheck_169_;
goto v_resetjp_163_;
}
v_resetjp_163_:
{
lean_object* v___x_167_; 
if (v_isShared_165_ == 0)
{
v___x_167_ = v___x_164_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_162_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
}
else
{
lean_object* v_a_170_; lean_object* v___x_172_; uint8_t v_isShared_173_; uint8_t v_isSharedCheck_177_; 
lean_dec(v_a_114_);
lean_dec(v_a_111_);
lean_dec(v_a_108_);
lean_dec(v_a_105_);
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_170_ = lean_ctor_get(v___x_116_, 0);
v_isSharedCheck_177_ = !lean_is_exclusive(v___x_116_);
if (v_isSharedCheck_177_ == 0)
{
v___x_172_ = v___x_116_;
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
else
{
lean_inc(v_a_170_);
lean_dec(v___x_116_);
v___x_172_ = lean_box(0);
v_isShared_173_ = v_isSharedCheck_177_;
goto v_resetjp_171_;
}
v_resetjp_171_:
{
lean_object* v___x_175_; 
if (v_isShared_173_ == 0)
{
v___x_175_ = v___x_172_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_176_; 
v_reuseFailAlloc_176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_176_, 0, v_a_170_);
v___x_175_ = v_reuseFailAlloc_176_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
return v___x_175_;
}
}
}
}
else
{
lean_object* v_a_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_185_; 
lean_dec(v_a_111_);
lean_dec(v_a_108_);
lean_dec(v_a_105_);
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_178_ = lean_ctor_get(v___x_113_, 0);
v_isSharedCheck_185_ = !lean_is_exclusive(v___x_113_);
if (v_isSharedCheck_185_ == 0)
{
v___x_180_ = v___x_113_;
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_a_178_);
lean_dec(v___x_113_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_185_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_183_; 
if (v_isShared_181_ == 0)
{
v___x_183_ = v___x_180_;
goto v_reusejp_182_;
}
else
{
lean_object* v_reuseFailAlloc_184_; 
v_reuseFailAlloc_184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_184_, 0, v_a_178_);
v___x_183_ = v_reuseFailAlloc_184_;
goto v_reusejp_182_;
}
v_reusejp_182_:
{
return v___x_183_;
}
}
}
}
else
{
lean_object* v_a_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_193_; 
lean_dec(v_a_108_);
lean_dec(v_a_105_);
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_186_ = lean_ctor_get(v___x_110_, 0);
v_isSharedCheck_193_ = !lean_is_exclusive(v___x_110_);
if (v_isSharedCheck_193_ == 0)
{
v___x_188_ = v___x_110_;
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_a_186_);
lean_dec(v___x_110_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_193_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_191_; 
if (v_isShared_189_ == 0)
{
v___x_191_ = v___x_188_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v_a_186_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
else
{
lean_object* v_a_194_; lean_object* v___x_196_; uint8_t v_isShared_197_; uint8_t v_isSharedCheck_201_; 
lean_dec(v_a_105_);
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_194_ = lean_ctor_get(v___x_107_, 0);
v_isSharedCheck_201_ = !lean_is_exclusive(v___x_107_);
if (v_isSharedCheck_201_ == 0)
{
v___x_196_ = v___x_107_;
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
else
{
lean_inc(v_a_194_);
lean_dec(v___x_107_);
v___x_196_ = lean_box(0);
v_isShared_197_ = v_isSharedCheck_201_;
goto v_resetjp_195_;
}
v_resetjp_195_:
{
lean_object* v___x_199_; 
if (v_isShared_197_ == 0)
{
v___x_199_ = v___x_196_;
goto v_reusejp_198_;
}
else
{
lean_object* v_reuseFailAlloc_200_; 
v_reuseFailAlloc_200_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_200_, 0, v_a_194_);
v___x_199_ = v_reuseFailAlloc_200_;
goto v_reusejp_198_;
}
v_reusejp_198_:
{
return v___x_199_;
}
}
}
}
else
{
lean_object* v_a_202_; lean_object* v___x_204_; uint8_t v_isShared_205_; uint8_t v_isSharedCheck_209_; 
lean_dec(v_a_102_);
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_202_ = lean_ctor_get(v___x_104_, 0);
v_isSharedCheck_209_ = !lean_is_exclusive(v___x_104_);
if (v_isSharedCheck_209_ == 0)
{
v___x_204_ = v___x_104_;
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
else
{
lean_inc(v_a_202_);
lean_dec(v___x_104_);
v___x_204_ = lean_box(0);
v_isShared_205_ = v_isSharedCheck_209_;
goto v_resetjp_203_;
}
v_resetjp_203_:
{
lean_object* v___x_207_; 
if (v_isShared_205_ == 0)
{
v___x_207_ = v___x_204_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v_a_202_);
v___x_207_ = v_reuseFailAlloc_208_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
return v___x_207_;
}
}
}
}
else
{
lean_object* v_a_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_217_; 
lean_dec(v_a_99_);
lean_dec(v_a_96_);
v_a_210_ = lean_ctor_get(v___x_101_, 0);
v_isSharedCheck_217_ = !lean_is_exclusive(v___x_101_);
if (v_isSharedCheck_217_ == 0)
{
v___x_212_ = v___x_101_;
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_a_210_);
lean_dec(v___x_101_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_217_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_a_210_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
return v___x_215_;
}
}
}
}
else
{
lean_object* v_a_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_225_; 
lean_dec(v_a_96_);
v_a_218_ = lean_ctor_get(v___x_98_, 0);
v_isSharedCheck_225_ = !lean_is_exclusive(v___x_98_);
if (v_isSharedCheck_225_ == 0)
{
v___x_220_ = v___x_98_;
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_a_218_);
lean_dec(v___x_98_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_225_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
lean_object* v___x_223_; 
if (v_isShared_221_ == 0)
{
v___x_223_ = v___x_220_;
goto v_reusejp_222_;
}
else
{
lean_object* v_reuseFailAlloc_224_; 
v_reuseFailAlloc_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_224_, 0, v_a_218_);
v___x_223_ = v_reuseFailAlloc_224_;
goto v_reusejp_222_;
}
v_reusejp_222_:
{
return v___x_223_;
}
}
}
}
else
{
lean_object* v_a_226_; lean_object* v___x_228_; uint8_t v_isShared_229_; uint8_t v_isSharedCheck_233_; 
v_a_226_ = lean_ctor_get(v___x_95_, 0);
v_isSharedCheck_233_ = !lean_is_exclusive(v___x_95_);
if (v_isSharedCheck_233_ == 0)
{
v___x_228_ = v___x_95_;
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
else
{
lean_inc(v_a_226_);
lean_dec(v___x_95_);
v___x_228_ = lean_box(0);
v_isShared_229_ = v_isSharedCheck_233_;
goto v_resetjp_227_;
}
v_resetjp_227_:
{
lean_object* v___x_231_; 
if (v_isShared_229_ == 0)
{
v___x_231_ = v___x_228_;
goto v_reusejp_230_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_a_226_);
v___x_231_ = v_reuseFailAlloc_232_;
goto v_reusejp_230_;
}
v_reusejp_230_:
{
return v___x_231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___boxed(lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_){
_start:
{
lean_object* v_res_239_; 
v_res_239_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRules(v_a_234_, v_a_235_, v_a_236_, v_a_237_);
lean_dec(v_a_237_);
lean_dec_ref(v_a_236_);
lean_dec(v_a_235_);
lean_dec_ref(v_a_234_);
return v_res_239_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__2(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_243_ = lean_box(0);
v___x_244_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__1));
v___x_245_ = l_Lean_Expr_const___override(v___x_244_, v___x_243_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__3(void){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_box(0);
v___x_248_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__2, &l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__2);
v___x_249_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_249_, 0, v___x_248_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
lean_ctor_set(v___x_249_, 2, v___x_247_);
lean_ctor_set(v___x_249_, 3, v___x_247_);
lean_ctor_set(v___x_249_, 4, v___x_246_);
return v___x_249_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default(void){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__3, &l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__3_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default___closed__3);
return v___x_250_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint(void){
_start:
{
lean_object* v___x_251_; 
v___x_251_ = l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default;
return v___x_251_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0(void){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_259_ = lean_box(1);
v___x_260_ = lean_unsigned_to_nat(0u);
v___x_261_ = lean_box(0);
v___x_262_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_instInhabitedSpecTheorems_default;
v___x_263_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_263_, 0, v___x_262_);
lean_ctor_set(v___x_263_, 1, v___x_261_);
lean_ctor_set(v___x_263_, 2, v___x_260_);
lean_ctor_set(v___x_263_, 3, v___x_259_);
lean_ctor_set(v___x_263_, 4, v___x_259_);
return v___x_263_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default(void){
_start:
{
lean_object* v___x_264_; 
v___x_264_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0, &l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0);
return v___x_264_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope(void){
_start:
{
lean_object* v___x_265_; 
v___x_265_ = l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default;
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(lean_object* v_s_266_, lean_object* v_thm_267_){
_start:
{
lean_object* v_specs_268_; lean_object* v_lastLiftedPre_x3f_269_; lean_object* v_nextDeclIdx_270_; lean_object* v_joinPoints_271_; lean_object* v_splitEqs_272_; lean_object* v___x_274_; uint8_t v_isShared_275_; uint8_t v_isSharedCheck_280_; 
v_specs_268_ = lean_ctor_get(v_s_266_, 0);
v_lastLiftedPre_x3f_269_ = lean_ctor_get(v_s_266_, 1);
v_nextDeclIdx_270_ = lean_ctor_get(v_s_266_, 2);
v_joinPoints_271_ = lean_ctor_get(v_s_266_, 3);
v_splitEqs_272_ = lean_ctor_get(v_s_266_, 4);
v_isSharedCheck_280_ = !lean_is_exclusive(v_s_266_);
if (v_isSharedCheck_280_ == 0)
{
v___x_274_ = v_s_266_;
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
else
{
lean_inc(v_splitEqs_272_);
lean_inc(v_joinPoints_271_);
lean_inc(v_nextDeclIdx_270_);
lean_inc(v_lastLiftedPre_x3f_269_);
lean_inc(v_specs_268_);
lean_dec(v_s_266_);
v___x_274_ = lean_box(0);
v_isShared_275_ = v_isSharedCheck_280_;
goto v_resetjp_273_;
}
v_resetjp_273_:
{
lean_object* v___x_276_; lean_object* v___x_278_; 
v___x_276_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_insert(v_specs_268_, v_thm_267_);
if (v_isShared_275_ == 0)
{
lean_ctor_set(v___x_274_, 0, v___x_276_);
v___x_278_ = v___x_274_;
goto v_reusejp_277_;
}
else
{
lean_object* v_reuseFailAlloc_279_; 
v_reuseFailAlloc_279_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_279_, 0, v___x_276_);
lean_ctor_set(v_reuseFailAlloc_279_, 1, v_lastLiftedPre_x3f_269_);
lean_ctor_set(v_reuseFailAlloc_279_, 2, v_nextDeclIdx_270_);
lean_ctor_set(v_reuseFailAlloc_279_, 3, v_joinPoints_271_);
lean_ctor_set(v_reuseFailAlloc_279_, 4, v_splitEqs_272_);
v___x_278_ = v_reuseFailAlloc_279_;
goto v_reusejp_277_;
}
v_reusejp_277_:
{
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object* v_x_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_){
_start:
{
lean_object* v___x_294_; 
lean_inc(v___y_288_);
lean_inc_ref(v___y_287_);
lean_inc(v___y_286_);
lean_inc_ref(v___y_285_);
lean_inc(v___y_284_);
lean_inc(v___y_283_);
lean_inc_ref(v___y_282_);
v___x_294_ = lean_apply_12(v_x_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_, v___y_289_, v___y_290_, v___y_291_, v___y_292_, lean_box(0));
return v___x_294_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object* v_x_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_, lean_object* v___y_302_, lean_object* v___y_303_, lean_object* v___y_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_, v___y_301_, v___y_302_, v___y_303_, v___y_304_, v___y_305_, v___y_306_);
lean_dec(v___y_302_);
lean_dec_ref(v___y_301_);
lean_dec(v___y_300_);
lean_dec_ref(v___y_299_);
lean_dec(v___y_298_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object* v_mvarId_309_, lean_object* v_x_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_){
_start:
{
lean_object* v___f_323_; lean_object* v___x_324_; 
lean_inc(v___y_317_);
lean_inc_ref(v___y_316_);
lean_inc(v___y_315_);
lean_inc_ref(v___y_314_);
lean_inc(v___y_313_);
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
v___f_323_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_323_, 0, v_x_310_);
lean_closure_set(v___f_323_, 1, v___y_311_);
lean_closure_set(v___f_323_, 2, v___y_312_);
lean_closure_set(v___f_323_, 3, v___y_313_);
lean_closure_set(v___f_323_, 4, v___y_314_);
lean_closure_set(v___f_323_, 5, v___y_315_);
lean_closure_set(v___f_323_, 6, v___y_316_);
lean_closure_set(v___f_323_, 7, v___y_317_);
v___x_324_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_309_, v___f_323_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
if (lean_obj_tag(v___x_324_) == 0)
{
return v___x_324_;
}
else
{
lean_object* v_a_325_; lean_object* v___x_327_; uint8_t v_isShared_328_; uint8_t v_isSharedCheck_332_; 
v_a_325_ = lean_ctor_get(v___x_324_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_324_);
if (v_isSharedCheck_332_ == 0)
{
v___x_327_ = v___x_324_;
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
else
{
lean_inc(v_a_325_);
lean_dec(v___x_324_);
v___x_327_ = lean_box(0);
v_isShared_328_ = v_isSharedCheck_332_;
goto v_resetjp_326_;
}
v_resetjp_326_:
{
lean_object* v___x_330_; 
if (v_isShared_328_ == 0)
{
v___x_330_ = v___x_327_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v_a_325_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object* v_mvarId_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_333_, v_x_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
lean_dec(v___y_345_);
lean_dec_ref(v___y_344_);
lean_dec(v___y_343_);
lean_dec_ref(v___y_342_);
lean_dec(v___y_341_);
lean_dec_ref(v___y_340_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec(v___y_336_);
lean_dec_ref(v___y_335_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(lean_object* v_00_u03b1_348_, lean_object* v_mvarId_349_, lean_object* v_x_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_, lean_object* v___y_356_, lean_object* v___y_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_){
_start:
{
lean_object* v___x_363_; 
v___x_363_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_349_, v_x_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_, v___y_356_, v___y_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_);
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object* v_00_u03b1_364_, lean_object* v_mvarId_365_, lean_object* v_x_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_){
_start:
{
lean_object* v_res_379_; 
v_res_379_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_364_, v_mvarId_365_, v_x_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_, v___y_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_);
lean_dec(v___y_377_);
lean_dec_ref(v___y_376_);
lean_dec(v___y_375_);
lean_dec_ref(v___y_374_);
lean_dec(v___y_373_);
lean_dec_ref(v___y_372_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object* v_as_380_, size_t v_i_381_, size_t v_stop_382_, lean_object* v_b_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_){
_start:
{
lean_object* v_a_390_; uint8_t v___x_394_; 
v___x_394_ = lean_usize_dec_eq(v_i_381_, v_stop_382_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; 
v___x_395_ = lean_array_uget_borrowed(v_as_380_, v_i_381_);
if (lean_obj_tag(v___x_395_) == 0)
{
v_a_390_ = v_b_383_;
goto v___jp_389_;
}
else
{
lean_object* v_val_396_; uint8_t v___x_397_; 
v_val_396_ = lean_ctor_get(v___x_395_, 0);
v___x_397_ = l_Lean_LocalDecl_isImplementationDetail(v_val_396_);
if (v___x_397_ == 0)
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_398_ = l_Lean_LocalDecl_fvarId(v_val_396_);
v___x_399_ = lean_unsigned_to_nat(100u);
v___x_400_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_mkSpecTheoremFromLocal(v___x_398_, v___x_399_, v___y_384_, v___y_385_, v___y_386_, v___y_387_);
if (lean_obj_tag(v___x_400_) == 0)
{
lean_object* v_a_401_; 
v_a_401_ = lean_ctor_get(v___x_400_, 0);
lean_inc(v_a_401_);
lean_dec_ref_known(v___x_400_, 1);
if (lean_obj_tag(v_a_401_) == 1)
{
lean_object* v_val_402_; lean_object* v___x_403_; 
v_val_402_ = lean_ctor_get(v_a_401_, 0);
lean_inc(v_val_402_);
lean_dec_ref_known(v_a_401_, 1);
v___x_403_ = l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(v_b_383_, v_val_402_);
v_a_390_ = v___x_403_;
goto v___jp_389_;
}
else
{
lean_dec(v_a_401_);
v_a_390_ = v_b_383_;
goto v___jp_389_;
}
}
else
{
lean_object* v_a_404_; lean_object* v___x_406_; uint8_t v_isShared_407_; uint8_t v_isSharedCheck_416_; 
v_a_404_ = lean_ctor_get(v___x_400_, 0);
v_isSharedCheck_416_ = !lean_is_exclusive(v___x_400_);
if (v_isSharedCheck_416_ == 0)
{
v___x_406_ = v___x_400_;
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
else
{
lean_inc(v_a_404_);
lean_dec(v___x_400_);
v___x_406_ = lean_box(0);
v_isShared_407_ = v_isSharedCheck_416_;
goto v_resetjp_405_;
}
v_resetjp_405_:
{
uint8_t v___x_408_; 
v___x_408_ = l_Lean_Exception_isInterrupt(v_a_404_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
lean_inc(v_a_404_);
v___x_409_ = l_Lean_Exception_isRuntime(v_a_404_);
if (v___x_409_ == 0)
{
lean_del_object(v___x_406_);
lean_dec(v_a_404_);
v_a_390_ = v_b_383_;
goto v___jp_389_;
}
else
{
lean_object* v___x_411_; 
lean_dec_ref(v_b_383_);
if (v_isShared_407_ == 0)
{
v___x_411_ = v___x_406_;
goto v_reusejp_410_;
}
else
{
lean_object* v_reuseFailAlloc_412_; 
v_reuseFailAlloc_412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_412_, 0, v_a_404_);
v___x_411_ = v_reuseFailAlloc_412_;
goto v_reusejp_410_;
}
v_reusejp_410_:
{
return v___x_411_;
}
}
}
else
{
lean_object* v___x_414_; 
lean_dec_ref(v_b_383_);
if (v_isShared_407_ == 0)
{
v___x_414_ = v___x_406_;
goto v_reusejp_413_;
}
else
{
lean_object* v_reuseFailAlloc_415_; 
v_reuseFailAlloc_415_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_415_, 0, v_a_404_);
v___x_414_ = v_reuseFailAlloc_415_;
goto v_reusejp_413_;
}
v_reusejp_413_:
{
return v___x_414_;
}
}
}
}
}
else
{
v_a_390_ = v_b_383_;
goto v___jp_389_;
}
}
}
else
{
lean_object* v___x_417_; 
v___x_417_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_417_, 0, v_b_383_);
return v___x_417_;
}
v___jp_389_:
{
size_t v___x_391_; size_t v___x_392_; 
v___x_391_ = ((size_t)1ULL);
v___x_392_ = lean_usize_add(v_i_381_, v___x_391_);
v_i_381_ = v___x_392_;
v_b_383_ = v_a_390_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_as_418_, lean_object* v_i_419_, lean_object* v_stop_420_, lean_object* v_b_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_){
_start:
{
size_t v_i_boxed_427_; size_t v_stop_boxed_428_; lean_object* v_res_429_; 
v_i_boxed_427_ = lean_unbox_usize(v_i_419_);
lean_dec(v_i_419_);
v_stop_boxed_428_ = lean_unbox_usize(v_stop_420_);
lean_dec(v_stop_420_);
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_418_, v_i_boxed_427_, v_stop_boxed_428_, v_b_421_, v___y_422_, v___y_423_, v___y_424_, v___y_425_);
lean_dec(v___y_425_);
lean_dec_ref(v___y_424_);
lean_dec(v___y_423_);
lean_dec_ref(v___y_422_);
lean_dec_ref(v_as_418_);
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object* v_x_430_, lean_object* v_x_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_){
_start:
{
if (lean_obj_tag(v_x_430_) == 0)
{
lean_object* v_cs_444_; lean_object* v___x_446_; uint8_t v_isShared_447_; uint8_t v_isSharedCheck_457_; 
v_cs_444_ = lean_ctor_get(v_x_430_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_457_ == 0)
{
v___x_446_ = v_x_430_;
v_isShared_447_ = v_isSharedCheck_457_;
goto v_resetjp_445_;
}
else
{
lean_inc(v_cs_444_);
lean_dec(v_x_430_);
v___x_446_ = lean_box(0);
v_isShared_447_ = v_isSharedCheck_457_;
goto v_resetjp_445_;
}
v_resetjp_445_:
{
lean_object* v___x_448_; lean_object* v___x_449_; uint8_t v___x_450_; 
v___x_448_ = lean_unsigned_to_nat(0u);
v___x_449_ = lean_array_get_size(v_cs_444_);
v___x_450_ = lean_nat_dec_lt(v___x_448_, v___x_449_);
if (v___x_450_ == 0)
{
lean_object* v___x_452_; 
lean_dec_ref(v_cs_444_);
if (v_isShared_447_ == 0)
{
lean_ctor_set(v___x_446_, 0, v_x_431_);
v___x_452_ = v___x_446_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v_x_431_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
return v___x_452_;
}
}
else
{
size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; 
lean_del_object(v___x_446_);
v___x_454_ = ((size_t)0ULL);
v___x_455_ = lean_usize_of_nat(v___x_449_);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_444_, v___x_454_, v___x_455_, v_x_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_, v___y_436_, v___y_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v_cs_444_);
return v___x_456_;
}
}
}
else
{
lean_object* v_vs_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_471_; 
v_vs_458_ = lean_ctor_get(v_x_430_, 0);
v_isSharedCheck_471_ = !lean_is_exclusive(v_x_430_);
if (v_isSharedCheck_471_ == 0)
{
v___x_460_ = v_x_430_;
v_isShared_461_ = v_isSharedCheck_471_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_vs_458_);
lean_dec(v_x_430_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_471_;
goto v_resetjp_459_;
}
v_resetjp_459_:
{
lean_object* v___x_462_; lean_object* v___x_463_; uint8_t v___x_464_; 
v___x_462_ = lean_unsigned_to_nat(0u);
v___x_463_ = lean_array_get_size(v_vs_458_);
v___x_464_ = lean_nat_dec_lt(v___x_462_, v___x_463_);
if (v___x_464_ == 0)
{
lean_object* v___x_466_; 
lean_dec_ref(v_vs_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 0);
lean_ctor_set(v___x_460_, 0, v_x_431_);
v___x_466_ = v___x_460_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_x_431_);
v___x_466_ = v_reuseFailAlloc_467_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
return v___x_466_;
}
}
else
{
size_t v___x_468_; size_t v___x_469_; lean_object* v___x_470_; 
lean_del_object(v___x_460_);
v___x_468_ = ((size_t)0ULL);
v___x_469_ = lean_usize_of_nat(v___x_463_);
v___x_470_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_458_, v___x_468_, v___x_469_, v_x_431_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec_ref(v_vs_458_);
return v___x_470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_472_, size_t v_i_473_, size_t v_stop_474_, lean_object* v_b_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_){
_start:
{
uint8_t v___x_488_; 
v___x_488_ = lean_usize_dec_eq(v_i_473_, v_stop_474_);
if (v___x_488_ == 0)
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_array_uget_borrowed(v_as_472_, v_i_473_);
lean_inc(v___x_489_);
v___x_490_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_489_, v_b_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_);
if (lean_obj_tag(v___x_490_) == 0)
{
lean_object* v_a_491_; size_t v___x_492_; size_t v___x_493_; 
v_a_491_ = lean_ctor_get(v___x_490_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v___x_490_, 1);
v___x_492_ = ((size_t)1ULL);
v___x_493_ = lean_usize_add(v_i_473_, v___x_492_);
v_i_473_ = v___x_493_;
v_b_475_ = v_a_491_;
goto _start;
}
else
{
return v___x_490_;
}
}
else
{
lean_object* v___x_495_; 
v___x_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_495_, 0, v_b_475_);
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_496_, lean_object* v_i_497_, lean_object* v_stop_498_, lean_object* v_b_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_){
_start:
{
size_t v_i_boxed_512_; size_t v_stop_boxed_513_; lean_object* v_res_514_; 
v_i_boxed_512_ = lean_unbox_usize(v_i_497_);
lean_dec(v_i_497_);
v_stop_boxed_513_ = lean_unbox_usize(v_stop_498_);
lean_dec(v_stop_498_);
v_res_514_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_496_, v_i_boxed_512_, v_stop_boxed_513_, v_b_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_);
lean_dec(v___y_510_);
lean_dec_ref(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec(v___y_506_);
lean_dec_ref(v___y_505_);
lean_dec(v___y_504_);
lean_dec_ref(v___y_503_);
lean_dec(v___y_502_);
lean_dec(v___y_501_);
lean_dec_ref(v___y_500_);
lean_dec_ref(v_as_496_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object* v_x_515_, lean_object* v_x_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_515_, v_x_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
lean_dec(v___y_523_);
lean_dec_ref(v___y_522_);
lean_dec(v___y_521_);
lean_dec_ref(v___y_520_);
lean_dec(v___y_519_);
lean_dec(v___y_518_);
lean_dec_ref(v___y_517_);
return v_res_529_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_530_; 
v___x_530_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object* v_x_531_, size_t v_x_532_, size_t v_x_533_, lean_object* v_x_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_){
_start:
{
if (lean_obj_tag(v_x_531_) == 0)
{
lean_object* v_cs_547_; lean_object* v___x_548_; size_t v___x_549_; lean_object* v_j_550_; lean_object* v___x_551_; size_t v___x_552_; size_t v___x_553_; size_t v___x_554_; size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; lean_object* v___x_558_; 
v_cs_547_ = lean_ctor_get(v_x_531_, 0);
lean_inc_ref(v_cs_547_);
lean_dec_ref_known(v_x_531_, 1);
v___x_548_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
v___x_549_ = lean_usize_shift_right(v_x_532_, v_x_533_);
v_j_550_ = lean_usize_to_nat(v___x_549_);
v___x_551_ = lean_array_get_borrowed(v___x_548_, v_cs_547_, v_j_550_);
v___x_552_ = ((size_t)1ULL);
v___x_553_ = lean_usize_shift_left(v___x_552_, v_x_533_);
v___x_554_ = lean_usize_sub(v___x_553_, v___x_552_);
v___x_555_ = lean_usize_land(v_x_532_, v___x_554_);
v___x_556_ = ((size_t)5ULL);
v___x_557_ = lean_usize_sub(v_x_533_, v___x_556_);
lean_inc(v___x_551_);
v___x_558_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_551_, v___x_555_, v___x_557_, v_x_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
if (lean_obj_tag(v___x_558_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; uint8_t v___x_563_; 
v_a_559_ = lean_ctor_get(v___x_558_, 0);
v___x_560_ = lean_unsigned_to_nat(1u);
v___x_561_ = lean_nat_add(v_j_550_, v___x_560_);
lean_dec(v_j_550_);
v___x_562_ = lean_array_get_size(v_cs_547_);
v___x_563_ = lean_nat_dec_lt(v___x_561_, v___x_562_);
if (v___x_563_ == 0)
{
lean_dec(v___x_561_);
lean_dec_ref(v_cs_547_);
return v___x_558_;
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
lean_inc(v_a_559_);
lean_dec_ref_known(v___x_558_, 1);
v___x_564_ = lean_usize_of_nat(v___x_561_);
lean_dec(v___x_561_);
v___x_565_ = lean_usize_of_nat(v___x_562_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_547_, v___x_564_, v___x_565_, v_a_559_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec_ref(v_cs_547_);
return v___x_566_;
}
}
else
{
lean_dec(v_j_550_);
lean_dec_ref(v_cs_547_);
return v___x_558_;
}
}
else
{
lean_object* v_vs_567_; lean_object* v___x_569_; uint8_t v_isShared_570_; uint8_t v_isSharedCheck_580_; 
v_vs_567_ = lean_ctor_get(v_x_531_, 0);
v_isSharedCheck_580_ = !lean_is_exclusive(v_x_531_);
if (v_isSharedCheck_580_ == 0)
{
v___x_569_ = v_x_531_;
v_isShared_570_ = v_isSharedCheck_580_;
goto v_resetjp_568_;
}
else
{
lean_inc(v_vs_567_);
lean_dec(v_x_531_);
v___x_569_ = lean_box(0);
v_isShared_570_ = v_isSharedCheck_580_;
goto v_resetjp_568_;
}
v_resetjp_568_:
{
lean_object* v___x_571_; lean_object* v___x_572_; uint8_t v___x_573_; 
v___x_571_ = lean_usize_to_nat(v_x_532_);
v___x_572_ = lean_array_get_size(v_vs_567_);
v___x_573_ = lean_nat_dec_lt(v___x_571_, v___x_572_);
if (v___x_573_ == 0)
{
lean_object* v___x_575_; 
lean_dec(v___x_571_);
lean_dec_ref(v_vs_567_);
if (v_isShared_570_ == 0)
{
lean_ctor_set_tag(v___x_569_, 0);
lean_ctor_set(v___x_569_, 0, v_x_534_);
v___x_575_ = v___x_569_;
goto v_reusejp_574_;
}
else
{
lean_object* v_reuseFailAlloc_576_; 
v_reuseFailAlloc_576_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_576_, 0, v_x_534_);
v___x_575_ = v_reuseFailAlloc_576_;
goto v_reusejp_574_;
}
v_reusejp_574_:
{
return v___x_575_;
}
}
else
{
size_t v___x_577_; size_t v___x_578_; lean_object* v___x_579_; 
lean_del_object(v___x_569_);
v___x_577_ = lean_usize_of_nat(v___x_571_);
lean_dec(v___x_571_);
v___x_578_ = lean_usize_of_nat(v___x_572_);
v___x_579_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_567_, v___x_577_, v___x_578_, v_x_534_, v___y_542_, v___y_543_, v___y_544_, v___y_545_);
lean_dec_ref(v_vs_567_);
return v___x_579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_581_, lean_object* v_x_582_, lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v___y_585_, lean_object* v___y_586_, lean_object* v___y_587_, lean_object* v___y_588_, lean_object* v___y_589_, lean_object* v___y_590_, lean_object* v___y_591_, lean_object* v___y_592_, lean_object* v___y_593_, lean_object* v___y_594_, lean_object* v___y_595_, lean_object* v___y_596_){
_start:
{
size_t v_x_19104__boxed_597_; size_t v_x_19105__boxed_598_; lean_object* v_res_599_; 
v_x_19104__boxed_597_ = lean_unbox_usize(v_x_582_);
lean_dec(v_x_582_);
v_x_19105__boxed_598_ = lean_unbox_usize(v_x_583_);
lean_dec(v_x_583_);
v_res_599_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_581_, v_x_19104__boxed_597_, v_x_19105__boxed_598_, v_x_584_, v___y_585_, v___y_586_, v___y_587_, v___y_588_, v___y_589_, v___y_590_, v___y_591_, v___y_592_, v___y_593_, v___y_594_, v___y_595_);
lean_dec(v___y_595_);
lean_dec_ref(v___y_594_);
lean_dec(v___y_593_);
lean_dec_ref(v___y_592_);
lean_dec(v___y_591_);
lean_dec_ref(v___y_590_);
lean_dec(v___y_589_);
lean_dec_ref(v___y_588_);
lean_dec(v___y_587_);
lean_dec(v___y_586_);
lean_dec_ref(v___y_585_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object* v_t_600_, lean_object* v_init_601_, lean_object* v_start_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_){
_start:
{
lean_object* v___x_615_; uint8_t v___x_616_; 
v___x_615_ = lean_unsigned_to_nat(0u);
v___x_616_ = lean_nat_dec_eq(v_start_602_, v___x_615_);
if (v___x_616_ == 0)
{
lean_object* v_root_617_; lean_object* v_tail_618_; size_t v_shift_619_; lean_object* v_tailOff_620_; uint8_t v___x_621_; 
v_root_617_ = lean_ctor_get(v_t_600_, 0);
lean_inc_ref(v_root_617_);
v_tail_618_ = lean_ctor_get(v_t_600_, 1);
lean_inc_ref(v_tail_618_);
v_shift_619_ = lean_ctor_get_usize(v_t_600_, 4);
v_tailOff_620_ = lean_ctor_get(v_t_600_, 3);
lean_inc(v_tailOff_620_);
lean_dec_ref(v_t_600_);
v___x_621_ = lean_nat_dec_le(v_tailOff_620_, v_start_602_);
if (v___x_621_ == 0)
{
size_t v___x_622_; lean_object* v___x_623_; 
lean_dec(v_tailOff_620_);
v___x_622_ = lean_usize_of_nat(v_start_602_);
v___x_623_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_617_, v___x_622_, v_shift_619_, v_init_601_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_623_) == 0)
{
lean_object* v_a_624_; lean_object* v___x_625_; uint8_t v___x_626_; 
v_a_624_ = lean_ctor_get(v___x_623_, 0);
v___x_625_ = lean_array_get_size(v_tail_618_);
v___x_626_ = lean_nat_dec_lt(v___x_615_, v___x_625_);
if (v___x_626_ == 0)
{
lean_dec_ref(v_tail_618_);
return v___x_623_;
}
else
{
size_t v___x_627_; size_t v___x_628_; lean_object* v___x_629_; 
lean_inc(v_a_624_);
lean_dec_ref_known(v___x_623_, 1);
v___x_627_ = ((size_t)0ULL);
v___x_628_ = lean_usize_of_nat(v___x_625_);
v___x_629_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_618_, v___x_627_, v___x_628_, v_a_624_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec_ref(v_tail_618_);
return v___x_629_;
}
}
else
{
lean_dec_ref(v_tail_618_);
return v___x_623_;
}
}
else
{
lean_object* v___x_630_; lean_object* v___x_631_; uint8_t v___x_632_; 
lean_dec_ref(v_root_617_);
v___x_630_ = lean_nat_sub(v_start_602_, v_tailOff_620_);
lean_dec(v_tailOff_620_);
v___x_631_ = lean_array_get_size(v_tail_618_);
v___x_632_ = lean_nat_dec_lt(v___x_630_, v___x_631_);
if (v___x_632_ == 0)
{
lean_object* v___x_633_; 
lean_dec(v___x_630_);
lean_dec_ref(v_tail_618_);
v___x_633_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_633_, 0, v_init_601_);
return v___x_633_;
}
else
{
size_t v___x_634_; size_t v___x_635_; lean_object* v___x_636_; 
v___x_634_ = lean_usize_of_nat(v___x_630_);
lean_dec(v___x_630_);
v___x_635_ = lean_usize_of_nat(v___x_631_);
v___x_636_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_618_, v___x_634_, v___x_635_, v_init_601_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec_ref(v_tail_618_);
return v___x_636_;
}
}
}
else
{
lean_object* v_root_637_; lean_object* v_tail_638_; lean_object* v___x_639_; 
v_root_637_ = lean_ctor_get(v_t_600_, 0);
lean_inc_ref(v_root_637_);
v_tail_638_ = lean_ctor_get(v_t_600_, 1);
lean_inc_ref(v_tail_638_);
lean_dec_ref(v_t_600_);
v___x_639_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_637_, v_init_601_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
if (lean_obj_tag(v___x_639_) == 0)
{
lean_object* v_a_640_; lean_object* v___x_641_; uint8_t v___x_642_; 
v_a_640_ = lean_ctor_get(v___x_639_, 0);
v___x_641_ = lean_array_get_size(v_tail_638_);
v___x_642_ = lean_nat_dec_lt(v___x_615_, v___x_641_);
if (v___x_642_ == 0)
{
lean_dec_ref(v_tail_638_);
return v___x_639_;
}
else
{
size_t v___x_643_; size_t v___x_644_; lean_object* v___x_645_; 
lean_inc(v_a_640_);
lean_dec_ref_known(v___x_639_, 1);
v___x_643_ = ((size_t)0ULL);
v___x_644_ = lean_usize_of_nat(v___x_641_);
v___x_645_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_638_, v___x_643_, v___x_644_, v_a_640_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec_ref(v_tail_638_);
return v___x_645_;
}
}
else
{
lean_dec_ref(v_tail_638_);
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object* v_t_646_, lean_object* v_init_647_, lean_object* v_start_648_, lean_object* v___y_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_646_, v_init_647_, v_start_648_, v___y_649_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_);
lean_dec(v___y_659_);
lean_dec_ref(v___y_658_);
lean_dec(v___y_657_);
lean_dec_ref(v___y_656_);
lean_dec(v___y_655_);
lean_dec_ref(v___y_654_);
lean_dec(v___y_653_);
lean_dec_ref(v___y_652_);
lean_dec(v___y_651_);
lean_dec(v___y_650_);
lean_dec_ref(v___y_649_);
lean_dec(v_start_648_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(lean_object* v_lctx_662_, lean_object* v_init_663_, lean_object* v_start_664_, lean_object* v___y_665_, lean_object* v___y_666_, lean_object* v___y_667_, lean_object* v___y_668_, lean_object* v___y_669_, lean_object* v___y_670_, lean_object* v___y_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_decls_677_; lean_object* v___x_678_; 
v_decls_677_ = lean_ctor_get(v_lctx_662_, 1);
lean_inc_ref(v_decls_677_);
lean_dec_ref(v_lctx_662_);
v___x_678_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_677_, v_init_663_, v_start_664_, v___y_665_, v___y_666_, v___y_667_, v___y_668_, v___y_669_, v___y_670_, v___y_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object* v_lctx_679_, lean_object* v_init_680_, lean_object* v_start_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_679_, v_init_680_, v_start_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_);
lean_dec(v___y_692_);
lean_dec_ref(v___y_691_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec(v___y_683_);
lean_dec_ref(v___y_682_);
lean_dec(v_start_681_);
return v_res_694_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(lean_object* v_scope_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_lctx_708_; lean_object* v_decls_709_; lean_object* v_nextDeclIdx_710_; lean_object* v_size_711_; uint8_t v___x_712_; 
v_lctx_708_ = lean_ctor_get(v___y_703_, 2);
v_decls_709_ = lean_ctor_get(v_lctx_708_, 1);
v_nextDeclIdx_710_ = lean_ctor_get(v_scope_695_, 2);
v_size_711_ = lean_ctor_get(v_decls_709_, 2);
v___x_712_ = lean_nat_dec_eq(v_nextDeclIdx_710_, v_size_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; 
lean_inc(v_nextDeclIdx_710_);
lean_inc_ref(v_lctx_708_);
v___x_713_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_708_, v_scope_695_, v_nextDeclIdx_710_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
lean_dec(v_nextDeclIdx_710_);
if (lean_obj_tag(v___x_713_) == 0)
{
lean_object* v_a_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_733_; 
v_a_714_ = lean_ctor_get(v___x_713_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v___x_713_);
if (v_isSharedCheck_733_ == 0)
{
v___x_716_ = v___x_713_;
v_isShared_717_ = v_isSharedCheck_733_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_a_714_);
lean_dec(v___x_713_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_733_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
lean_object* v_specs_718_; lean_object* v_lastLiftedPre_x3f_719_; lean_object* v_joinPoints_720_; lean_object* v_splitEqs_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_731_; 
v_specs_718_ = lean_ctor_get(v_a_714_, 0);
v_lastLiftedPre_x3f_719_ = lean_ctor_get(v_a_714_, 1);
v_joinPoints_720_ = lean_ctor_get(v_a_714_, 3);
v_splitEqs_721_ = lean_ctor_get(v_a_714_, 4);
v_isSharedCheck_731_ = !lean_is_exclusive(v_a_714_);
if (v_isSharedCheck_731_ == 0)
{
lean_object* v_unused_732_; 
v_unused_732_ = lean_ctor_get(v_a_714_, 2);
lean_dec(v_unused_732_);
v___x_723_ = v_a_714_;
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_splitEqs_721_);
lean_inc(v_joinPoints_720_);
lean_inc(v_lastLiftedPre_x3f_719_);
lean_inc(v_specs_718_);
lean_dec(v_a_714_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_731_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
lean_inc(v_size_711_);
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 2, v_size_711_);
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v_specs_718_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_lastLiftedPre_x3f_719_);
lean_ctor_set(v_reuseFailAlloc_730_, 2, v_size_711_);
lean_ctor_set(v_reuseFailAlloc_730_, 3, v_joinPoints_720_);
lean_ctor_set(v_reuseFailAlloc_730_, 4, v_splitEqs_721_);
v___x_726_ = v_reuseFailAlloc_730_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
lean_object* v___x_728_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v___x_726_);
v___x_728_ = v___x_716_;
goto v_reusejp_727_;
}
else
{
lean_object* v_reuseFailAlloc_729_; 
v_reuseFailAlloc_729_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_729_, 0, v___x_726_);
v___x_728_ = v_reuseFailAlloc_729_;
goto v_reusejp_727_;
}
v_reusejp_727_:
{
return v___x_728_;
}
}
}
}
}
else
{
return v___x_713_;
}
}
else
{
lean_object* v___x_734_; 
v___x_734_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_734_, 0, v_scope_695_);
return v___x_734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object* v_scope_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(v_scope_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec_ref(v___y_743_);
lean_dec(v___y_742_);
lean_dec_ref(v___y_741_);
lean_dec(v___y_740_);
lean_dec_ref(v___y_739_);
lean_dec(v___y_738_);
lean_dec(v___y_737_);
lean_dec_ref(v___y_736_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(lean_object* v_scope_749_, lean_object* v_goal_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_, lean_object* v_a_758_, lean_object* v_a_759_, lean_object* v_a_760_, lean_object* v_a_761_){
_start:
{
lean_object* v___f_763_; lean_object* v___x_764_; 
v___f_763_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_763_, 0, v_scope_749_);
v___x_764_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_750_, v___f_763_, v_a_751_, v_a_752_, v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_, v_a_758_, v_a_759_, v_a_760_, v_a_761_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___boxed(lean_object* v_scope_765_, lean_object* v_goal_766_, lean_object* v_a_767_, lean_object* v_a_768_, lean_object* v_a_769_, lean_object* v_a_770_, lean_object* v_a_771_, lean_object* v_a_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_){
_start:
{
lean_object* v_res_779_; 
v_res_779_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_765_, v_goal_766_, v_a_767_, v_a_768_, v_a_769_, v_a_770_, v_a_771_, v_a_772_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_);
lean_dec(v_a_777_);
lean_dec_ref(v_a_776_);
lean_dec(v_a_775_);
lean_dec_ref(v_a_774_);
lean_dec(v_a_773_);
lean_dec_ref(v_a_772_);
lean_dec(v_a_771_);
lean_dec_ref(v_a_770_);
lean_dec(v_a_769_);
lean_dec(v_a_768_);
lean_dec_ref(v_a_767_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object* v_as_780_, size_t v_i_781_, size_t v_stop_782_, lean_object* v_b_783_, lean_object* v___y_784_, lean_object* v___y_785_, lean_object* v___y_786_, lean_object* v___y_787_, lean_object* v___y_788_, lean_object* v___y_789_, lean_object* v___y_790_, lean_object* v___y_791_, lean_object* v___y_792_, lean_object* v___y_793_, lean_object* v___y_794_){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_780_, v_i_781_, v_stop_782_, v_b_783_, v___y_791_, v___y_792_, v___y_793_, v___y_794_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object* v_as_797_, lean_object* v_i_798_, lean_object* v_stop_799_, lean_object* v_b_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_){
_start:
{
size_t v_i_boxed_813_; size_t v_stop_boxed_814_; lean_object* v_res_815_; 
v_i_boxed_813_ = lean_unbox_usize(v_i_798_);
lean_dec(v_i_798_);
v_stop_boxed_814_ = lean_unbox_usize(v_stop_799_);
lean_dec(v_stop_799_);
v_res_815_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_797_, v_i_boxed_813_, v_stop_boxed_814_, v_b_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_);
lean_dec(v___y_811_);
lean_dec_ref(v___y_810_);
lean_dec(v___y_809_);
lean_dec_ref(v___y_808_);
lean_dec(v___y_807_);
lean_dec_ref(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec(v___y_802_);
lean_dec_ref(v___y_801_);
lean_dec_ref(v_as_797_);
return v_res_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(lean_object* v_a_816_){
_start:
{
lean_object* v___x_818_; lean_object* v_fuel_823_; 
v___x_818_ = lean_st_ref_get(v_a_816_);
v_fuel_823_ = lean_ctor_get(v___x_818_, 10);
lean_inc(v_fuel_823_);
lean_dec(v___x_818_);
if (lean_obj_tag(v_fuel_823_) == 0)
{
lean_object* v_n_824_; lean_object* v___x_826_; uint8_t v_isShared_827_; uint8_t v_isSharedCheck_834_; 
v_n_824_ = lean_ctor_get(v_fuel_823_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v_fuel_823_);
if (v_isSharedCheck_834_ == 0)
{
v___x_826_ = v_fuel_823_;
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
else
{
lean_inc(v_n_824_);
lean_dec(v_fuel_823_);
v___x_826_ = lean_box(0);
v_isShared_827_ = v_isSharedCheck_834_;
goto v_resetjp_825_;
}
v_resetjp_825_:
{
lean_object* v___x_828_; uint8_t v___x_829_; 
v___x_828_ = lean_unsigned_to_nat(0u);
v___x_829_ = lean_nat_dec_eq(v_n_824_, v___x_828_);
lean_dec(v_n_824_);
if (v___x_829_ == 0)
{
lean_del_object(v___x_826_);
goto v___jp_819_;
}
else
{
lean_object* v___x_830_; lean_object* v___x_832_; 
v___x_830_ = lean_box(v___x_829_);
if (v_isShared_827_ == 0)
{
lean_ctor_set(v___x_826_, 0, v___x_830_);
v___x_832_ = v___x_826_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v___x_830_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
else
{
lean_dec(v_fuel_823_);
goto v___jp_819_;
}
v___jp_819_:
{
uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = 0;
v___x_821_ = lean_box(v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg___boxed(lean_object* v_a_835_, lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_835_);
lean_dec(v_a_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel(lean_object* v_a_838_, lean_object* v_a_839_, lean_object* v_a_840_, lean_object* v_a_841_, lean_object* v_a_842_, lean_object* v_a_843_, lean_object* v_a_844_, lean_object* v_a_845_, lean_object* v_a_846_, lean_object* v_a_847_, lean_object* v_a_848_){
_start:
{
lean_object* v___x_850_; 
v___x_850_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_839_);
return v___x_850_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___boxed(lean_object* v_a_851_, lean_object* v_a_852_, lean_object* v_a_853_, lean_object* v_a_854_, lean_object* v_a_855_, lean_object* v_a_856_, lean_object* v_a_857_, lean_object* v_a_858_, lean_object* v_a_859_, lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l_Lean_Elab_Tactic_VCGen_outOfFuel(v_a_851_, v_a_852_, v_a_853_, v_a_854_, v_a_855_, v_a_856_, v_a_857_, v_a_858_, v_a_859_, v_a_860_, v_a_861_);
lean_dec(v_a_861_);
lean_dec_ref(v_a_860_);
lean_dec(v_a_859_);
lean_dec_ref(v_a_858_);
lean_dec(v_a_857_);
lean_dec_ref(v_a_856_);
lean_dec(v_a_855_);
lean_dec_ref(v_a_854_);
lean_dec(v_a_853_);
lean_dec(v_a_852_);
lean_dec_ref(v_a_851_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg(lean_object* v_a_864_){
_start:
{
lean_object* v___x_866_; lean_object* v_specBackwardRuleCache_867_; lean_object* v_wpSplitBackwardRuleCache_868_; lean_object* v_assertionSplitBackwardRuleCache_869_; lean_object* v_latticeBackwardRuleCache_870_; lean_object* v_frameBackwardRuleCache_871_; lean_object* v_rintroBackwardRuleCache_872_; lean_object* v_frameDB_873_; lean_object* v_invariants_874_; lean_object* v_vcs_875_; lean_object* v_simpState_876_; lean_object* v_fuel_877_; lean_object* v_pendingJoinPoints_878_; lean_object* v___x_880_; uint8_t v_isShared_881_; uint8_t v_isSharedCheck_903_; 
v___x_866_ = lean_st_ref_take(v_a_864_);
v_specBackwardRuleCache_867_ = lean_ctor_get(v___x_866_, 0);
v_wpSplitBackwardRuleCache_868_ = lean_ctor_get(v___x_866_, 1);
v_assertionSplitBackwardRuleCache_869_ = lean_ctor_get(v___x_866_, 2);
v_latticeBackwardRuleCache_870_ = lean_ctor_get(v___x_866_, 3);
v_frameBackwardRuleCache_871_ = lean_ctor_get(v___x_866_, 4);
v_rintroBackwardRuleCache_872_ = lean_ctor_get(v___x_866_, 5);
v_frameDB_873_ = lean_ctor_get(v___x_866_, 6);
v_invariants_874_ = lean_ctor_get(v___x_866_, 7);
v_vcs_875_ = lean_ctor_get(v___x_866_, 8);
v_simpState_876_ = lean_ctor_get(v___x_866_, 9);
v_fuel_877_ = lean_ctor_get(v___x_866_, 10);
v_pendingJoinPoints_878_ = lean_ctor_get(v___x_866_, 11);
v_isSharedCheck_903_ = !lean_is_exclusive(v___x_866_);
if (v_isSharedCheck_903_ == 0)
{
v___x_880_ = v___x_866_;
v_isShared_881_ = v_isSharedCheck_903_;
goto v_resetjp_879_;
}
else
{
lean_inc(v_pendingJoinPoints_878_);
lean_inc(v_fuel_877_);
lean_inc(v_simpState_876_);
lean_inc(v_vcs_875_);
lean_inc(v_invariants_874_);
lean_inc(v_frameDB_873_);
lean_inc(v_rintroBackwardRuleCache_872_);
lean_inc(v_frameBackwardRuleCache_871_);
lean_inc(v_latticeBackwardRuleCache_870_);
lean_inc(v_assertionSplitBackwardRuleCache_869_);
lean_inc(v_wpSplitBackwardRuleCache_868_);
lean_inc(v_specBackwardRuleCache_867_);
lean_dec(v___x_866_);
v___x_880_ = lean_box(0);
v_isShared_881_ = v_isSharedCheck_903_;
goto v_resetjp_879_;
}
v_resetjp_879_:
{
lean_object* v___x_882_; lean_object* v___y_884_; 
v___x_882_ = lean_box(0);
if (lean_obj_tag(v_fuel_877_) == 0)
{
lean_object* v_n_890_; lean_object* v_zero_891_; uint8_t v_isZero_892_; 
v_n_890_ = lean_ctor_get(v_fuel_877_, 0);
v_zero_891_ = lean_unsigned_to_nat(0u);
v_isZero_892_ = lean_nat_dec_eq(v_n_890_, v_zero_891_);
if (v_isZero_892_ == 0)
{
lean_object* v___x_894_; uint8_t v_isShared_895_; uint8_t v_isSharedCheck_901_; 
lean_inc(v_n_890_);
v_isSharedCheck_901_ = !lean_is_exclusive(v_fuel_877_);
if (v_isSharedCheck_901_ == 0)
{
lean_object* v_unused_902_; 
v_unused_902_ = lean_ctor_get(v_fuel_877_, 0);
lean_dec(v_unused_902_);
v___x_894_ = v_fuel_877_;
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
else
{
lean_dec(v_fuel_877_);
v___x_894_ = lean_box(0);
v_isShared_895_ = v_isSharedCheck_901_;
goto v_resetjp_893_;
}
v_resetjp_893_:
{
lean_object* v_one_896_; lean_object* v_n_897_; lean_object* v___x_899_; 
v_one_896_ = lean_unsigned_to_nat(1u);
v_n_897_ = lean_nat_sub(v_n_890_, v_one_896_);
lean_dec(v_n_890_);
if (v_isShared_895_ == 0)
{
lean_ctor_set(v___x_894_, 0, v_n_897_);
v___x_899_ = v___x_894_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_n_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
v___y_884_ = v___x_899_;
goto v___jp_883_;
}
}
}
else
{
v___y_884_ = v_fuel_877_;
goto v___jp_883_;
}
}
else
{
v___y_884_ = v_fuel_877_;
goto v___jp_883_;
}
v___jp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_881_ == 0)
{
lean_ctor_set(v___x_880_, 10, v___y_884_);
v___x_886_ = v___x_880_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_specBackwardRuleCache_867_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_wpSplitBackwardRuleCache_868_);
lean_ctor_set(v_reuseFailAlloc_889_, 2, v_assertionSplitBackwardRuleCache_869_);
lean_ctor_set(v_reuseFailAlloc_889_, 3, v_latticeBackwardRuleCache_870_);
lean_ctor_set(v_reuseFailAlloc_889_, 4, v_frameBackwardRuleCache_871_);
lean_ctor_set(v_reuseFailAlloc_889_, 5, v_rintroBackwardRuleCache_872_);
lean_ctor_set(v_reuseFailAlloc_889_, 6, v_frameDB_873_);
lean_ctor_set(v_reuseFailAlloc_889_, 7, v_invariants_874_);
lean_ctor_set(v_reuseFailAlloc_889_, 8, v_vcs_875_);
lean_ctor_set(v_reuseFailAlloc_889_, 9, v_simpState_876_);
lean_ctor_set(v_reuseFailAlloc_889_, 10, v___y_884_);
lean_ctor_set(v_reuseFailAlloc_889_, 11, v_pendingJoinPoints_878_);
v___x_886_ = v_reuseFailAlloc_889_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
lean_object* v___x_887_; lean_object* v___x_888_; 
v___x_887_ = lean_st_ref_put(v_a_864_, v___x_886_);
v___x_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_888_, 0, v___x_882_);
return v___x_888_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg___boxed(lean_object* v_a_904_, lean_object* v_a_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_904_);
lean_dec(v_a_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne(lean_object* v_a_907_, lean_object* v_a_908_, lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_){
_start:
{
lean_object* v___x_919_; 
v___x_919_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_908_);
return v___x_919_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___boxed(lean_object* v_a_920_, lean_object* v_a_921_, lean_object* v_a_922_, lean_object* v_a_923_, lean_object* v_a_924_, lean_object* v_a_925_, lean_object* v_a_926_, lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_){
_start:
{
lean_object* v_res_932_; 
v_res_932_ = l_Lean_Elab_Tactic_VCGen_burnOne(v_a_920_, v_a_921_, v_a_922_, v_a_923_, v_a_924_, v_a_925_, v_a_926_, v_a_927_, v_a_928_, v_a_929_, v_a_930_);
lean_dec(v_a_930_);
lean_dec_ref(v_a_929_);
lean_dec(v_a_928_);
lean_dec_ref(v_a_927_);
lean_dec(v_a_926_);
lean_dec_ref(v_a_925_);
lean_dec(v_a_924_);
lean_dec_ref(v_a_923_);
lean_dec(v_a_922_);
lean_dec(v_a_921_);
lean_dec_ref(v_a_920_);
return v_res_932_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__0(void){
_start:
{
lean_object* v___x_933_; 
v___x_933_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__1(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; 
v___x_934_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__0, &l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__0);
v___x_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_935_, 0, v___x_934_);
return v___x_935_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__2(void){
_start:
{
lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; 
v___x_936_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__1, &l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__1_once, _init_l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__1);
v___x_937_ = lean_unsigned_to_nat(0u);
v___x_938_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_938_, 0, v___x_937_);
lean_ctor_set(v___x_938_, 1, v___x_936_);
lean_ctor_set(v___x_938_, 2, v___x_936_);
lean_ctor_set(v___x_938_, 3, v___x_936_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg(lean_object* v_methods_939_, lean_object* v_k_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_){
_start:
{
lean_object* v___x_950_; lean_object* v_specBackwardRuleCache_951_; lean_object* v_wpSplitBackwardRuleCache_952_; lean_object* v_assertionSplitBackwardRuleCache_953_; lean_object* v_latticeBackwardRuleCache_954_; lean_object* v_frameBackwardRuleCache_955_; lean_object* v_rintroBackwardRuleCache_956_; lean_object* v_frameDB_957_; lean_object* v_invariants_958_; lean_object* v_vcs_959_; lean_object* v_simpState_960_; lean_object* v_fuel_961_; lean_object* v_pendingJoinPoints_962_; lean_object* v___x_964_; uint8_t v_isShared_965_; uint8_t v_isSharedCheck_1012_; 
v___x_950_ = lean_st_ref_take(v_a_942_);
v_specBackwardRuleCache_951_ = lean_ctor_get(v___x_950_, 0);
v_wpSplitBackwardRuleCache_952_ = lean_ctor_get(v___x_950_, 1);
v_assertionSplitBackwardRuleCache_953_ = lean_ctor_get(v___x_950_, 2);
v_latticeBackwardRuleCache_954_ = lean_ctor_get(v___x_950_, 3);
v_frameBackwardRuleCache_955_ = lean_ctor_get(v___x_950_, 4);
v_rintroBackwardRuleCache_956_ = lean_ctor_get(v___x_950_, 5);
v_frameDB_957_ = lean_ctor_get(v___x_950_, 6);
v_invariants_958_ = lean_ctor_get(v___x_950_, 7);
v_vcs_959_ = lean_ctor_get(v___x_950_, 8);
v_simpState_960_ = lean_ctor_get(v___x_950_, 9);
v_fuel_961_ = lean_ctor_get(v___x_950_, 10);
v_pendingJoinPoints_962_ = lean_ctor_get(v___x_950_, 11);
v_isSharedCheck_1012_ = !lean_is_exclusive(v___x_950_);
if (v_isSharedCheck_1012_ == 0)
{
v___x_964_ = v___x_950_;
v_isShared_965_ = v_isSharedCheck_1012_;
goto v_resetjp_963_;
}
else
{
lean_inc(v_pendingJoinPoints_962_);
lean_inc(v_fuel_961_);
lean_inc(v_simpState_960_);
lean_inc(v_vcs_959_);
lean_inc(v_invariants_958_);
lean_inc(v_frameDB_957_);
lean_inc(v_rintroBackwardRuleCache_956_);
lean_inc(v_frameBackwardRuleCache_955_);
lean_inc(v_latticeBackwardRuleCache_954_);
lean_inc(v_assertionSplitBackwardRuleCache_953_);
lean_inc(v_wpSplitBackwardRuleCache_952_);
lean_inc(v_specBackwardRuleCache_951_);
lean_dec(v___x_950_);
v___x_964_ = lean_box(0);
v_isShared_965_ = v_isSharedCheck_1012_;
goto v_resetjp_963_;
}
v_resetjp_963_:
{
lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_966_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__2, &l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__2_once, _init_l_Lean_Elab_Tactic_VCGen_runSimp___redArg___closed__2);
if (v_isShared_965_ == 0)
{
lean_ctor_set(v___x_964_, 9, v___x_966_);
v___x_968_ = v___x_964_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_1011_; 
v_reuseFailAlloc_1011_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_1011_, 0, v_specBackwardRuleCache_951_);
lean_ctor_set(v_reuseFailAlloc_1011_, 1, v_wpSplitBackwardRuleCache_952_);
lean_ctor_set(v_reuseFailAlloc_1011_, 2, v_assertionSplitBackwardRuleCache_953_);
lean_ctor_set(v_reuseFailAlloc_1011_, 3, v_latticeBackwardRuleCache_954_);
lean_ctor_set(v_reuseFailAlloc_1011_, 4, v_frameBackwardRuleCache_955_);
lean_ctor_set(v_reuseFailAlloc_1011_, 5, v_rintroBackwardRuleCache_956_);
lean_ctor_set(v_reuseFailAlloc_1011_, 6, v_frameDB_957_);
lean_ctor_set(v_reuseFailAlloc_1011_, 7, v_invariants_958_);
lean_ctor_set(v_reuseFailAlloc_1011_, 8, v_vcs_959_);
lean_ctor_set(v_reuseFailAlloc_1011_, 9, v___x_966_);
lean_ctor_set(v_reuseFailAlloc_1011_, 10, v_fuel_961_);
lean_ctor_set(v_reuseFailAlloc_1011_, 11, v_pendingJoinPoints_962_);
v___x_968_ = v_reuseFailAlloc_1011_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
lean_object* v___x_969_; lean_object* v_simpConfig_970_; lean_object* v___x_971_; 
v___x_969_ = lean_st_ref_put(v_a_942_, v___x_968_);
v_simpConfig_970_ = lean_ctor_get(v_a_941_, 4);
lean_inc_ref(v_simpConfig_970_);
v___x_971_ = l_Lean_Meta_Sym_Simp_SimpM_run___redArg(v_k_940_, v_methods_939_, v_simpConfig_970_, v_simpState_960_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_);
if (lean_obj_tag(v___x_971_) == 0)
{
lean_object* v_a_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_1002_; 
v_a_972_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1002_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1002_ == 0)
{
v___x_974_ = v___x_971_;
v_isShared_975_ = v_isSharedCheck_1002_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_a_972_);
lean_dec(v___x_971_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_1002_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v_fst_976_; lean_object* v_snd_977_; lean_object* v___x_978_; lean_object* v_specBackwardRuleCache_979_; lean_object* v_wpSplitBackwardRuleCache_980_; lean_object* v_assertionSplitBackwardRuleCache_981_; lean_object* v_latticeBackwardRuleCache_982_; lean_object* v_frameBackwardRuleCache_983_; lean_object* v_rintroBackwardRuleCache_984_; lean_object* v_frameDB_985_; lean_object* v_invariants_986_; lean_object* v_vcs_987_; lean_object* v_fuel_988_; lean_object* v_pendingJoinPoints_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_1000_; 
v_fst_976_ = lean_ctor_get(v_a_972_, 0);
lean_inc(v_fst_976_);
v_snd_977_ = lean_ctor_get(v_a_972_, 1);
lean_inc(v_snd_977_);
lean_dec(v_a_972_);
v___x_978_ = lean_st_ref_take(v_a_942_);
v_specBackwardRuleCache_979_ = lean_ctor_get(v___x_978_, 0);
v_wpSplitBackwardRuleCache_980_ = lean_ctor_get(v___x_978_, 1);
v_assertionSplitBackwardRuleCache_981_ = lean_ctor_get(v___x_978_, 2);
v_latticeBackwardRuleCache_982_ = lean_ctor_get(v___x_978_, 3);
v_frameBackwardRuleCache_983_ = lean_ctor_get(v___x_978_, 4);
v_rintroBackwardRuleCache_984_ = lean_ctor_get(v___x_978_, 5);
v_frameDB_985_ = lean_ctor_get(v___x_978_, 6);
v_invariants_986_ = lean_ctor_get(v___x_978_, 7);
v_vcs_987_ = lean_ctor_get(v___x_978_, 8);
v_fuel_988_ = lean_ctor_get(v___x_978_, 10);
v_pendingJoinPoints_989_ = lean_ctor_get(v___x_978_, 11);
v_isSharedCheck_1000_ = !lean_is_exclusive(v___x_978_);
if (v_isSharedCheck_1000_ == 0)
{
lean_object* v_unused_1001_; 
v_unused_1001_ = lean_ctor_get(v___x_978_, 9);
lean_dec(v_unused_1001_);
v___x_991_ = v___x_978_;
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_pendingJoinPoints_989_);
lean_inc(v_fuel_988_);
lean_inc(v_vcs_987_);
lean_inc(v_invariants_986_);
lean_inc(v_frameDB_985_);
lean_inc(v_rintroBackwardRuleCache_984_);
lean_inc(v_frameBackwardRuleCache_983_);
lean_inc(v_latticeBackwardRuleCache_982_);
lean_inc(v_assertionSplitBackwardRuleCache_981_);
lean_inc(v_wpSplitBackwardRuleCache_980_);
lean_inc(v_specBackwardRuleCache_979_);
lean_dec(v___x_978_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_1000_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_994_; 
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 9, v_snd_977_);
v___x_994_ = v___x_991_;
goto v_reusejp_993_;
}
else
{
lean_object* v_reuseFailAlloc_999_; 
v_reuseFailAlloc_999_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_999_, 0, v_specBackwardRuleCache_979_);
lean_ctor_set(v_reuseFailAlloc_999_, 1, v_wpSplitBackwardRuleCache_980_);
lean_ctor_set(v_reuseFailAlloc_999_, 2, v_assertionSplitBackwardRuleCache_981_);
lean_ctor_set(v_reuseFailAlloc_999_, 3, v_latticeBackwardRuleCache_982_);
lean_ctor_set(v_reuseFailAlloc_999_, 4, v_frameBackwardRuleCache_983_);
lean_ctor_set(v_reuseFailAlloc_999_, 5, v_rintroBackwardRuleCache_984_);
lean_ctor_set(v_reuseFailAlloc_999_, 6, v_frameDB_985_);
lean_ctor_set(v_reuseFailAlloc_999_, 7, v_invariants_986_);
lean_ctor_set(v_reuseFailAlloc_999_, 8, v_vcs_987_);
lean_ctor_set(v_reuseFailAlloc_999_, 9, v_snd_977_);
lean_ctor_set(v_reuseFailAlloc_999_, 10, v_fuel_988_);
lean_ctor_set(v_reuseFailAlloc_999_, 11, v_pendingJoinPoints_989_);
v___x_994_ = v_reuseFailAlloc_999_;
goto v_reusejp_993_;
}
v_reusejp_993_:
{
lean_object* v___x_995_; lean_object* v___x_997_; 
v___x_995_ = lean_st_ref_put(v_a_942_, v___x_994_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v_fst_976_);
v___x_997_ = v___x_974_;
goto v_reusejp_996_;
}
else
{
lean_object* v_reuseFailAlloc_998_; 
v_reuseFailAlloc_998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_998_, 0, v_fst_976_);
v___x_997_ = v_reuseFailAlloc_998_;
goto v_reusejp_996_;
}
v_reusejp_996_:
{
return v___x_997_;
}
}
}
}
}
else
{
lean_object* v_a_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1010_; 
v_a_1003_ = lean_ctor_get(v___x_971_, 0);
v_isSharedCheck_1010_ = !lean_is_exclusive(v___x_971_);
if (v_isSharedCheck_1010_ == 0)
{
v___x_1005_ = v___x_971_;
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_a_1003_);
lean_dec(v___x_971_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1010_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1008_; 
if (v_isShared_1006_ == 0)
{
v___x_1008_ = v___x_1005_;
goto v_reusejp_1007_;
}
else
{
lean_object* v_reuseFailAlloc_1009_; 
v_reuseFailAlloc_1009_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1009_, 0, v_a_1003_);
v___x_1008_ = v_reuseFailAlloc_1009_;
goto v_reusejp_1007_;
}
v_reusejp_1007_:
{
return v___x_1008_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___redArg___boxed(lean_object* v_methods_1013_, lean_object* v_k_1014_, lean_object* v_a_1015_, lean_object* v_a_1016_, lean_object* v_a_1017_, lean_object* v_a_1018_, lean_object* v_a_1019_, lean_object* v_a_1020_, lean_object* v_a_1021_, lean_object* v_a_1022_, lean_object* v_a_1023_){
_start:
{
lean_object* v_res_1024_; 
v_res_1024_ = l_Lean_Elab_Tactic_VCGen_runSimp___redArg(v_methods_1013_, v_k_1014_, v_a_1015_, v_a_1016_, v_a_1017_, v_a_1018_, v_a_1019_, v_a_1020_, v_a_1021_, v_a_1022_);
lean_dec(v_a_1022_);
lean_dec_ref(v_a_1021_);
lean_dec(v_a_1020_);
lean_dec_ref(v_a_1019_);
lean_dec(v_a_1018_);
lean_dec_ref(v_a_1017_);
lean_dec(v_a_1016_);
lean_dec_ref(v_a_1015_);
return v_res_1024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_runSimp(lean_object* v_00_u03b1_1025_, lean_object* v_methods_1026_, lean_object* v_k_1027_, lean_object* v_a_1028_, lean_object* v_a_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_, lean_object* v_a_1032_, lean_object* v_a_1033_, lean_object* v_a_1034_, lean_object* v_a_1035_, lean_object* v_a_1036_, lean_object* v_a_1037_, lean_object* v_a_1038_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l_Lean_Elab_Tactic_VCGen_runSimp___redArg(v_methods_1026_, v_k_1027_, v_a_1028_, v_a_1029_, v_a_1033_, v_a_1034_, v_a_1035_, v_a_1036_, v_a_1037_, v_a_1038_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_runSimp___boxed(lean_object* v_00_u03b1_1041_, lean_object* v_methods_1042_, lean_object* v_k_1043_, lean_object* v_a_1044_, lean_object* v_a_1045_, lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l_Lean_Elab_Tactic_VCGen_runSimp(v_00_u03b1_1041_, v_methods_1042_, v_k_1043_, v_a_1044_, v_a_1045_, v_a_1046_, v_a_1047_, v_a_1048_, v_a_1049_, v_a_1050_, v_a_1051_, v_a_1052_, v_a_1053_, v_a_1054_);
lean_dec(v_a_1054_);
lean_dec_ref(v_a_1053_);
lean_dec(v_a_1052_);
lean_dec_ref(v_a_1051_);
lean_dec(v_a_1050_);
lean_dec_ref(v_a_1049_);
lean_dec(v_a_1048_);
lean_dec_ref(v_a_1047_);
lean_dec(v_a_1046_);
lean_dec(v_a_1045_);
lean_dec_ref(v_a_1044_);
return v_res_1056_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_SpecDB(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_RIntroAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_SpecDB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_RIntroAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default = _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry_default);
l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry = _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_instInhabitedFrameEntry);
l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB = _init_l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_instInhabitedFrameDB);
l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default = _init_l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint_default);
l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint = _init_l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_instInhabitedJoinPoint);
l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default = _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default);
l_Lean_Elab_Tactic_VCGen_instInhabitedScope = _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope();
lean_mark_persistent(l_Lean_Elab_Tactic_VCGen_instInhabitedScope);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_SpecDB(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_FrameProc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_VCGen_RIntroAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_SpecDB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_FrameProc(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Apply(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_DiscrTree(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_VCGen_RIntroAttr(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_VCGen_Context(builtin);
}
#ifdef __cplusplus
}
#endif
