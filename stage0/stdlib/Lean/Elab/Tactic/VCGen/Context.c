// Lean compiler output
// Module: Lean.Elab.Tactic.VCGen.Context
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Basic public import Lean.Elab.Tactic.VCGen.SpecDB public import Lean.Elab.Tactic.VCGen.FrameProc public import Lean.Meta.Sym.Apply public import Lean.Meta.Sym.Simp.DiscrTree public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
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
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
extern lean_object* l_Lean_Elab_Tactic_VCGen_SpecAttr_instInhabitedSpecTheorems_default;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
extern lean_object* l_Lean_Meta_Sym_instInhabitedPattern_default;
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
static lean_once_cell_t l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_registerJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0(void){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_box(0);
v___x_242_ = lean_box(1);
v___x_243_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_instInhabitedSpecTheorems_default;
v___x_244_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_244_, 0, v___x_243_);
lean_ctor_set(v___x_244_, 1, v___x_242_);
lean_ctor_set(v___x_244_, 2, v___x_241_);
lean_ctor_set(v___x_244_, 3, v___x_240_);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0, &l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default;
return v___x_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_registerJP(lean_object* v_s_247_, lean_object* v_fv_248_, lean_object* v_info_249_){
_start:
{
lean_object* v_specs_250_; lean_object* v_jps_251_; lean_object* v_lastLiftedPre_x3f_252_; lean_object* v_nextDeclIdx_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_261_; 
v_specs_250_ = lean_ctor_get(v_s_247_, 0);
v_jps_251_ = lean_ctor_get(v_s_247_, 1);
v_lastLiftedPre_x3f_252_ = lean_ctor_get(v_s_247_, 2);
v_nextDeclIdx_253_ = lean_ctor_get(v_s_247_, 3);
v_isSharedCheck_261_ = !lean_is_exclusive(v_s_247_);
if (v_isSharedCheck_261_ == 0)
{
v___x_255_ = v_s_247_;
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_nextDeclIdx_253_);
lean_inc(v_lastLiftedPre_x3f_252_);
lean_inc(v_jps_251_);
lean_inc(v_specs_250_);
lean_dec(v_s_247_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_261_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_257_; lean_object* v___x_259_; 
v___x_257_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_248_, v_info_249_, v_jps_251_);
if (v_isShared_256_ == 0)
{
lean_ctor_set(v___x_255_, 1, v___x_257_);
v___x_259_ = v___x_255_;
goto v_reusejp_258_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v_specs_250_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_257_);
lean_ctor_set(v_reuseFailAlloc_260_, 2, v_lastLiftedPre_x3f_252_);
lean_ctor_set(v_reuseFailAlloc_260_, 3, v_nextDeclIdx_253_);
v___x_259_ = v_reuseFailAlloc_260_;
goto v_reusejp_258_;
}
v_reusejp_258_:
{
return v___x_259_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(lean_object* v_t_262_, lean_object* v_k_263_){
_start:
{
if (lean_obj_tag(v_t_262_) == 0)
{
lean_object* v_k_264_; lean_object* v_v_265_; lean_object* v_l_266_; lean_object* v_r_267_; uint8_t v___x_268_; 
v_k_264_ = lean_ctor_get(v_t_262_, 1);
v_v_265_ = lean_ctor_get(v_t_262_, 2);
v_l_266_ = lean_ctor_get(v_t_262_, 3);
v_r_267_ = lean_ctor_get(v_t_262_, 4);
v___x_268_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_263_, v_k_264_);
switch(v___x_268_)
{
case 0:
{
v_t_262_ = v_l_266_;
goto _start;
}
case 1:
{
lean_object* v___x_270_; 
lean_inc(v_v_265_);
v___x_270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_270_, 0, v_v_265_);
return v___x_270_;
}
default: 
{
v_t_262_ = v_r_267_;
goto _start;
}
}
}
else
{
lean_object* v___x_272_; 
v___x_272_ = lean_box(0);
return v___x_272_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_273_, lean_object* v_k_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_273_, v_k_274_);
lean_dec(v_k_274_);
lean_dec(v_t_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f(lean_object* v_s_276_, lean_object* v_fv_277_){
_start:
{
lean_object* v_jps_278_; lean_object* v___x_279_; 
v_jps_278_ = lean_ctor_get(v_s_276_, 1);
v___x_279_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_jps_278_, v_fv_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f___boxed(lean_object* v_s_280_, lean_object* v_fv_281_){
_start:
{
lean_object* v_res_282_; 
v_res_282_ = l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f(v_s_280_, v_fv_281_);
lean_dec(v_fv_281_);
lean_dec_ref(v_s_280_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0(lean_object* v_00_u03b4_283_, lean_object* v_t_284_, lean_object* v_k_285_){
_start:
{
lean_object* v___x_286_; 
v___x_286_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_284_, v_k_285_);
return v___x_286_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_287_, lean_object* v_t_288_, lean_object* v_k_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0(v_00_u03b4_287_, v_t_288_, v_k_289_);
lean_dec(v_k_289_);
lean_dec(v_t_288_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(lean_object* v_s_291_, lean_object* v_thm_292_){
_start:
{
lean_object* v_specs_293_; lean_object* v_jps_294_; lean_object* v_lastLiftedPre_x3f_295_; lean_object* v_nextDeclIdx_296_; lean_object* v___x_298_; uint8_t v_isShared_299_; uint8_t v_isSharedCheck_304_; 
v_specs_293_ = lean_ctor_get(v_s_291_, 0);
v_jps_294_ = lean_ctor_get(v_s_291_, 1);
v_lastLiftedPre_x3f_295_ = lean_ctor_get(v_s_291_, 2);
v_nextDeclIdx_296_ = lean_ctor_get(v_s_291_, 3);
v_isSharedCheck_304_ = !lean_is_exclusive(v_s_291_);
if (v_isSharedCheck_304_ == 0)
{
v___x_298_ = v_s_291_;
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
else
{
lean_inc(v_nextDeclIdx_296_);
lean_inc(v_lastLiftedPre_x3f_295_);
lean_inc(v_jps_294_);
lean_inc(v_specs_293_);
lean_dec(v_s_291_);
v___x_298_ = lean_box(0);
v_isShared_299_ = v_isSharedCheck_304_;
goto v_resetjp_297_;
}
v_resetjp_297_:
{
lean_object* v___x_300_; lean_object* v___x_302_; 
v___x_300_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_insert(v_specs_293_, v_thm_292_);
if (v_isShared_299_ == 0)
{
lean_ctor_set(v___x_298_, 0, v___x_300_);
v___x_302_ = v___x_298_;
goto v_reusejp_301_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_300_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_jps_294_);
lean_ctor_set(v_reuseFailAlloc_303_, 2, v_lastLiftedPre_x3f_295_);
lean_ctor_set(v_reuseFailAlloc_303_, 3, v_nextDeclIdx_296_);
v___x_302_ = v_reuseFailAlloc_303_;
goto v_reusejp_301_;
}
v_reusejp_301_:
{
return v___x_302_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object* v_x_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_){
_start:
{
lean_object* v___x_318_; 
lean_inc(v___y_312_);
lean_inc_ref(v___y_311_);
lean_inc(v___y_310_);
lean_inc_ref(v___y_309_);
lean_inc(v___y_308_);
lean_inc(v___y_307_);
lean_inc_ref(v___y_306_);
v___x_318_ = lean_apply_12(v_x_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, lean_box(0));
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object* v_x_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_){
_start:
{
lean_object* v_res_332_; 
v_res_332_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec_ref(v___y_323_);
lean_dec(v___y_322_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
return v_res_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object* v_mvarId_333_, lean_object* v_x_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_){
_start:
{
lean_object* v___f_347_; lean_object* v___x_348_; 
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
lean_inc(v___y_339_);
lean_inc_ref(v___y_338_);
lean_inc(v___y_337_);
lean_inc(v___y_336_);
lean_inc_ref(v___y_335_);
v___f_347_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_347_, 0, v_x_334_);
lean_closure_set(v___f_347_, 1, v___y_335_);
lean_closure_set(v___f_347_, 2, v___y_336_);
lean_closure_set(v___f_347_, 3, v___y_337_);
lean_closure_set(v___f_347_, 4, v___y_338_);
lean_closure_set(v___f_347_, 5, v___y_339_);
lean_closure_set(v___f_347_, 6, v___y_340_);
lean_closure_set(v___f_347_, 7, v___y_341_);
v___x_348_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_333_, v___f_347_, v___y_342_, v___y_343_, v___y_344_, v___y_345_);
if (lean_obj_tag(v___x_348_) == 0)
{
return v___x_348_;
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
v_a_349_ = lean_ctor_get(v___x_348_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_348_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_348_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_348_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v___x_354_; 
if (v_isShared_352_ == 0)
{
v___x_354_ = v___x_351_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_a_349_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
return v___x_354_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object* v_mvarId_357_, lean_object* v_x_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_){
_start:
{
lean_object* v_res_371_; 
v_res_371_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_357_, v_x_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
lean_dec(v___y_361_);
lean_dec(v___y_360_);
lean_dec_ref(v___y_359_);
return v_res_371_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(lean_object* v_00_u03b1_372_, lean_object* v_mvarId_373_, lean_object* v_x_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_){
_start:
{
lean_object* v___x_387_; 
v___x_387_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_373_, v_x_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_);
return v___x_387_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object* v_00_u03b1_388_, lean_object* v_mvarId_389_, lean_object* v_x_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_){
_start:
{
lean_object* v_res_403_; 
v_res_403_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_388_, v_mvarId_389_, v_x_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec_ref(v___y_396_);
lean_dec(v___y_395_);
lean_dec_ref(v___y_394_);
lean_dec(v___y_393_);
lean_dec(v___y_392_);
lean_dec_ref(v___y_391_);
return v_res_403_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object* v_as_404_, size_t v_i_405_, size_t v_stop_406_, lean_object* v_b_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_){
_start:
{
lean_object* v_a_414_; uint8_t v___x_418_; 
v___x_418_ = lean_usize_dec_eq(v_i_405_, v_stop_406_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_array_uget_borrowed(v_as_404_, v_i_405_);
if (lean_obj_tag(v___x_419_) == 0)
{
v_a_414_ = v_b_407_;
goto v___jp_413_;
}
else
{
lean_object* v_val_420_; uint8_t v___x_421_; 
v_val_420_ = lean_ctor_get(v___x_419_, 0);
v___x_421_ = l_Lean_LocalDecl_isAuxDecl(v_val_420_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_422_ = l_Lean_LocalDecl_fvarId(v_val_420_);
v___x_423_ = lean_unsigned_to_nat(100u);
v___x_424_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_mkSpecTheoremFromLocal(v___x_422_, v___x_423_, v___y_408_, v___y_409_, v___y_410_, v___y_411_);
if (lean_obj_tag(v___x_424_) == 0)
{
lean_object* v_a_425_; 
v_a_425_ = lean_ctor_get(v___x_424_, 0);
lean_inc(v_a_425_);
lean_dec_ref_known(v___x_424_, 1);
if (lean_obj_tag(v_a_425_) == 1)
{
lean_object* v_val_426_; lean_object* v___x_427_; 
v_val_426_ = lean_ctor_get(v_a_425_, 0);
lean_inc(v_val_426_);
lean_dec_ref_known(v_a_425_, 1);
v___x_427_ = l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(v_b_407_, v_val_426_);
v_a_414_ = v___x_427_;
goto v___jp_413_;
}
else
{
lean_dec(v_a_425_);
v_a_414_ = v_b_407_;
goto v___jp_413_;
}
}
else
{
lean_object* v_a_428_; lean_object* v___x_430_; uint8_t v_isShared_431_; uint8_t v_isSharedCheck_439_; 
v_a_428_ = lean_ctor_get(v___x_424_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_424_);
if (v_isSharedCheck_439_ == 0)
{
v___x_430_ = v___x_424_;
v_isShared_431_ = v_isSharedCheck_439_;
goto v_resetjp_429_;
}
else
{
lean_inc(v_a_428_);
lean_dec(v___x_424_);
v___x_430_ = lean_box(0);
v_isShared_431_ = v_isSharedCheck_439_;
goto v_resetjp_429_;
}
v_resetjp_429_:
{
uint8_t v___y_433_; uint8_t v___x_437_; 
v___x_437_ = l_Lean_Exception_isInterrupt(v_a_428_);
if (v___x_437_ == 0)
{
uint8_t v___x_438_; 
lean_inc(v_a_428_);
v___x_438_ = l_Lean_Exception_isRuntime(v_a_428_);
v___y_433_ = v___x_438_;
goto v___jp_432_;
}
else
{
v___y_433_ = v___x_437_;
goto v___jp_432_;
}
v___jp_432_:
{
if (v___y_433_ == 0)
{
lean_del_object(v___x_430_);
lean_dec(v_a_428_);
v_a_414_ = v_b_407_;
goto v___jp_413_;
}
else
{
lean_object* v___x_435_; 
lean_dec_ref(v_b_407_);
if (v_isShared_431_ == 0)
{
v___x_435_ = v___x_430_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_a_428_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
}
else
{
v_a_414_ = v_b_407_;
goto v___jp_413_;
}
}
}
else
{
lean_object* v___x_440_; 
v___x_440_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_440_, 0, v_b_407_);
return v___x_440_;
}
v___jp_413_:
{
size_t v___x_415_; size_t v___x_416_; 
v___x_415_ = ((size_t)1ULL);
v___x_416_ = lean_usize_add(v_i_405_, v___x_415_);
v_i_405_ = v___x_416_;
v_b_407_ = v_a_414_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_as_441_, lean_object* v_i_442_, lean_object* v_stop_443_, lean_object* v_b_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_){
_start:
{
size_t v_i_boxed_450_; size_t v_stop_boxed_451_; lean_object* v_res_452_; 
v_i_boxed_450_ = lean_unbox_usize(v_i_442_);
lean_dec(v_i_442_);
v_stop_boxed_451_ = lean_unbox_usize(v_stop_443_);
lean_dec(v_stop_443_);
v_res_452_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_441_, v_i_boxed_450_, v_stop_boxed_451_, v_b_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec_ref(v_as_441_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object* v_x_453_, lean_object* v_x_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
if (lean_obj_tag(v_x_453_) == 0)
{
lean_object* v_cs_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_480_; 
v_cs_467_ = lean_ctor_get(v_x_453_, 0);
v_isSharedCheck_480_ = !lean_is_exclusive(v_x_453_);
if (v_isSharedCheck_480_ == 0)
{
v___x_469_ = v_x_453_;
v_isShared_470_ = v_isSharedCheck_480_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_cs_467_);
lean_dec(v_x_453_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_480_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_472_; uint8_t v___x_473_; 
v___x_471_ = lean_unsigned_to_nat(0u);
v___x_472_ = lean_array_get_size(v_cs_467_);
v___x_473_ = lean_nat_dec_lt(v___x_471_, v___x_472_);
if (v___x_473_ == 0)
{
lean_object* v___x_475_; 
lean_dec_ref(v_cs_467_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v_x_454_);
v___x_475_ = v___x_469_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v_x_454_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
else
{
size_t v___x_477_; size_t v___x_478_; lean_object* v___x_479_; 
lean_del_object(v___x_469_);
v___x_477_ = ((size_t)0ULL);
v___x_478_ = lean_usize_of_nat(v___x_472_);
v___x_479_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_467_, v___x_477_, v___x_478_, v_x_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec_ref(v_cs_467_);
return v___x_479_;
}
}
}
else
{
lean_object* v_vs_481_; lean_object* v___x_483_; uint8_t v_isShared_484_; uint8_t v_isSharedCheck_494_; 
v_vs_481_ = lean_ctor_get(v_x_453_, 0);
v_isSharedCheck_494_ = !lean_is_exclusive(v_x_453_);
if (v_isSharedCheck_494_ == 0)
{
v___x_483_ = v_x_453_;
v_isShared_484_ = v_isSharedCheck_494_;
goto v_resetjp_482_;
}
else
{
lean_inc(v_vs_481_);
lean_dec(v_x_453_);
v___x_483_ = lean_box(0);
v_isShared_484_ = v_isSharedCheck_494_;
goto v_resetjp_482_;
}
v_resetjp_482_:
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; 
v___x_485_ = lean_unsigned_to_nat(0u);
v___x_486_ = lean_array_get_size(v_vs_481_);
v___x_487_ = lean_nat_dec_lt(v___x_485_, v___x_486_);
if (v___x_487_ == 0)
{
lean_object* v___x_489_; 
lean_dec_ref(v_vs_481_);
if (v_isShared_484_ == 0)
{
lean_ctor_set_tag(v___x_483_, 0);
lean_ctor_set(v___x_483_, 0, v_x_454_);
v___x_489_ = v___x_483_;
goto v_reusejp_488_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_x_454_);
v___x_489_ = v_reuseFailAlloc_490_;
goto v_reusejp_488_;
}
v_reusejp_488_:
{
return v___x_489_;
}
}
else
{
size_t v___x_491_; size_t v___x_492_; lean_object* v___x_493_; 
lean_del_object(v___x_483_);
v___x_491_ = ((size_t)0ULL);
v___x_492_ = lean_usize_of_nat(v___x_486_);
v___x_493_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_481_, v___x_491_, v___x_492_, v_x_454_, v___y_462_, v___y_463_, v___y_464_, v___y_465_);
lean_dec_ref(v_vs_481_);
return v___x_493_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_495_, size_t v_i_496_, size_t v_stop_497_, lean_object* v_b_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_, lean_object* v___y_503_, lean_object* v___y_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_){
_start:
{
uint8_t v___x_511_; 
v___x_511_ = lean_usize_dec_eq(v_i_496_, v_stop_497_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_array_uget_borrowed(v_as_495_, v_i_496_);
lean_inc(v___x_512_);
v___x_513_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_512_, v_b_498_, v___y_499_, v___y_500_, v___y_501_, v___y_502_, v___y_503_, v___y_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v_a_514_; size_t v___x_515_; size_t v___x_516_; 
v_a_514_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_a_514_);
lean_dec_ref_known(v___x_513_, 1);
v___x_515_ = ((size_t)1ULL);
v___x_516_ = lean_usize_add(v_i_496_, v___x_515_);
v_i_496_ = v___x_516_;
v_b_498_ = v_a_514_;
goto _start;
}
else
{
return v___x_513_;
}
}
else
{
lean_object* v___x_518_; 
v___x_518_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_518_, 0, v_b_498_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_519_, lean_object* v_i_520_, lean_object* v_stop_521_, lean_object* v_b_522_, lean_object* v___y_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_){
_start:
{
size_t v_i_boxed_535_; size_t v_stop_boxed_536_; lean_object* v_res_537_; 
v_i_boxed_535_ = lean_unbox_usize(v_i_520_);
lean_dec(v_i_520_);
v_stop_boxed_536_ = lean_unbox_usize(v_stop_521_);
lean_dec(v_stop_521_);
v_res_537_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_519_, v_i_boxed_535_, v_stop_boxed_536_, v_b_522_, v___y_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_);
lean_dec(v___y_533_);
lean_dec_ref(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec(v___y_527_);
lean_dec_ref(v___y_526_);
lean_dec(v___y_525_);
lean_dec(v___y_524_);
lean_dec_ref(v___y_523_);
lean_dec_ref(v_as_519_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object* v_x_538_, lean_object* v_x_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_538_, v_x_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_);
lean_dec(v___y_550_);
lean_dec_ref(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec(v___y_541_);
lean_dec_ref(v___y_540_);
return v_res_552_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object* v_x_554_, size_t v_x_555_, size_t v_x_556_, lean_object* v_x_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_){
_start:
{
if (lean_obj_tag(v_x_554_) == 0)
{
lean_object* v_cs_570_; lean_object* v___x_571_; size_t v___x_572_; lean_object* v_j_573_; lean_object* v___x_574_; size_t v___x_575_; size_t v___x_576_; size_t v___x_577_; size_t v___x_578_; size_t v___x_579_; size_t v___x_580_; lean_object* v___x_581_; 
v_cs_570_ = lean_ctor_get(v_x_554_, 0);
lean_inc_ref(v_cs_570_);
lean_dec_ref_known(v_x_554_, 1);
v___x_571_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
v___x_572_ = lean_usize_shift_right(v_x_555_, v_x_556_);
v_j_573_ = lean_usize_to_nat(v___x_572_);
v___x_574_ = lean_array_get_borrowed(v___x_571_, v_cs_570_, v_j_573_);
v___x_575_ = ((size_t)1ULL);
v___x_576_ = lean_usize_shift_left(v___x_575_, v_x_556_);
v___x_577_ = lean_usize_sub(v___x_576_, v___x_575_);
v___x_578_ = lean_usize_land(v_x_555_, v___x_577_);
v___x_579_ = ((size_t)5ULL);
v___x_580_ = lean_usize_sub(v_x_556_, v___x_579_);
lean_inc(v___x_574_);
v___x_581_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_574_, v___x_578_, v___x_580_, v_x_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
if (lean_obj_tag(v___x_581_) == 0)
{
lean_object* v_a_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; uint8_t v___x_586_; 
v_a_582_ = lean_ctor_get(v___x_581_, 0);
lean_inc(v_a_582_);
v___x_583_ = lean_unsigned_to_nat(1u);
v___x_584_ = lean_nat_add(v_j_573_, v___x_583_);
lean_dec(v_j_573_);
v___x_585_ = lean_array_get_size(v_cs_570_);
v___x_586_ = lean_nat_dec_lt(v___x_584_, v___x_585_);
if (v___x_586_ == 0)
{
lean_dec(v___x_584_);
lean_dec(v_a_582_);
lean_dec_ref(v_cs_570_);
return v___x_581_;
}
else
{
size_t v___x_587_; size_t v___x_588_; lean_object* v___x_589_; 
lean_dec_ref_known(v___x_581_, 1);
v___x_587_ = lean_usize_of_nat(v___x_584_);
lean_dec(v___x_584_);
v___x_588_ = lean_usize_of_nat(v___x_585_);
v___x_589_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_570_, v___x_587_, v___x_588_, v_a_582_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec_ref(v_cs_570_);
return v___x_589_;
}
}
else
{
lean_dec(v_j_573_);
lean_dec_ref(v_cs_570_);
return v___x_581_;
}
}
else
{
lean_object* v_vs_590_; lean_object* v___x_592_; uint8_t v_isShared_593_; uint8_t v_isSharedCheck_603_; 
v_vs_590_ = lean_ctor_get(v_x_554_, 0);
v_isSharedCheck_603_ = !lean_is_exclusive(v_x_554_);
if (v_isSharedCheck_603_ == 0)
{
v___x_592_ = v_x_554_;
v_isShared_593_ = v_isSharedCheck_603_;
goto v_resetjp_591_;
}
else
{
lean_inc(v_vs_590_);
lean_dec(v_x_554_);
v___x_592_ = lean_box(0);
v_isShared_593_ = v_isSharedCheck_603_;
goto v_resetjp_591_;
}
v_resetjp_591_:
{
lean_object* v___x_594_; lean_object* v___x_595_; uint8_t v___x_596_; 
v___x_594_ = lean_usize_to_nat(v_x_555_);
v___x_595_ = lean_array_get_size(v_vs_590_);
v___x_596_ = lean_nat_dec_lt(v___x_594_, v___x_595_);
if (v___x_596_ == 0)
{
lean_object* v___x_598_; 
lean_dec(v___x_594_);
lean_dec_ref(v_vs_590_);
if (v_isShared_593_ == 0)
{
lean_ctor_set_tag(v___x_592_, 0);
lean_ctor_set(v___x_592_, 0, v_x_557_);
v___x_598_ = v___x_592_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_599_; 
v_reuseFailAlloc_599_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_599_, 0, v_x_557_);
v___x_598_ = v_reuseFailAlloc_599_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
return v___x_598_;
}
}
else
{
size_t v___x_600_; size_t v___x_601_; lean_object* v___x_602_; 
lean_del_object(v___x_592_);
v___x_600_ = lean_usize_of_nat(v___x_594_);
lean_dec(v___x_594_);
v___x_601_ = lean_usize_of_nat(v___x_595_);
v___x_602_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_590_, v___x_600_, v___x_601_, v_x_557_, v___y_565_, v___y_566_, v___y_567_, v___y_568_);
lean_dec_ref(v_vs_590_);
return v___x_602_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_604_, lean_object* v_x_605_, lean_object* v_x_606_, lean_object* v_x_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_, lean_object* v___y_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_){
_start:
{
size_t v_x_19154__boxed_620_; size_t v_x_19155__boxed_621_; lean_object* v_res_622_; 
v_x_19154__boxed_620_ = lean_unbox_usize(v_x_605_);
lean_dec(v_x_605_);
v_x_19155__boxed_621_ = lean_unbox_usize(v_x_606_);
lean_dec(v_x_606_);
v_res_622_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_604_, v_x_19154__boxed_620_, v_x_19155__boxed_621_, v_x_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_, v___y_614_, v___y_615_, v___y_616_, v___y_617_, v___y_618_);
lean_dec(v___y_618_);
lean_dec_ref(v___y_617_);
lean_dec(v___y_616_);
lean_dec_ref(v___y_615_);
lean_dec(v___y_614_);
lean_dec_ref(v___y_613_);
lean_dec(v___y_612_);
lean_dec_ref(v___y_611_);
lean_dec(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object* v_t_623_, lean_object* v_init_624_, lean_object* v_start_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
lean_object* v___x_638_; uint8_t v___x_639_; 
v___x_638_ = lean_unsigned_to_nat(0u);
v___x_639_ = lean_nat_dec_eq(v_start_625_, v___x_638_);
if (v___x_639_ == 0)
{
lean_object* v_root_640_; lean_object* v_tail_641_; size_t v_shift_642_; lean_object* v_tailOff_643_; uint8_t v___x_644_; 
v_root_640_ = lean_ctor_get(v_t_623_, 0);
lean_inc_ref(v_root_640_);
v_tail_641_ = lean_ctor_get(v_t_623_, 1);
lean_inc_ref(v_tail_641_);
v_shift_642_ = lean_ctor_get_usize(v_t_623_, 4);
v_tailOff_643_ = lean_ctor_get(v_t_623_, 3);
lean_inc(v_tailOff_643_);
lean_dec_ref(v_t_623_);
v___x_644_ = lean_nat_dec_le(v_tailOff_643_, v_start_625_);
if (v___x_644_ == 0)
{
size_t v___x_645_; lean_object* v___x_646_; 
lean_dec(v_tailOff_643_);
v___x_645_ = lean_usize_of_nat(v_start_625_);
v___x_646_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_640_, v___x_645_, v_shift_642_, v_init_624_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_646_) == 0)
{
lean_object* v_a_647_; lean_object* v___x_648_; uint8_t v___x_649_; 
v_a_647_ = lean_ctor_get(v___x_646_, 0);
lean_inc(v_a_647_);
v___x_648_ = lean_array_get_size(v_tail_641_);
v___x_649_ = lean_nat_dec_lt(v___x_638_, v___x_648_);
if (v___x_649_ == 0)
{
lean_dec(v_a_647_);
lean_dec_ref(v_tail_641_);
return v___x_646_;
}
else
{
size_t v___x_650_; size_t v___x_651_; lean_object* v___x_652_; 
lean_dec_ref_known(v___x_646_, 1);
v___x_650_ = ((size_t)0ULL);
v___x_651_ = lean_usize_of_nat(v___x_648_);
v___x_652_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_641_, v___x_650_, v___x_651_, v_a_647_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_tail_641_);
return v___x_652_;
}
}
else
{
lean_dec_ref(v_tail_641_);
return v___x_646_;
}
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; uint8_t v___x_655_; 
lean_dec_ref(v_root_640_);
v___x_653_ = lean_nat_sub(v_start_625_, v_tailOff_643_);
lean_dec(v_tailOff_643_);
v___x_654_ = lean_array_get_size(v_tail_641_);
v___x_655_ = lean_nat_dec_lt(v___x_653_, v___x_654_);
if (v___x_655_ == 0)
{
lean_object* v___x_656_; 
lean_dec(v___x_653_);
lean_dec_ref(v_tail_641_);
v___x_656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_656_, 0, v_init_624_);
return v___x_656_;
}
else
{
size_t v___x_657_; size_t v___x_658_; lean_object* v___x_659_; 
v___x_657_ = lean_usize_of_nat(v___x_653_);
lean_dec(v___x_653_);
v___x_658_ = lean_usize_of_nat(v___x_654_);
v___x_659_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_641_, v___x_657_, v___x_658_, v_init_624_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_tail_641_);
return v___x_659_;
}
}
}
else
{
lean_object* v_root_660_; lean_object* v_tail_661_; lean_object* v___x_662_; 
v_root_660_ = lean_ctor_get(v_t_623_, 0);
lean_inc_ref(v_root_660_);
v_tail_661_ = lean_ctor_get(v_t_623_, 1);
lean_inc_ref(v_tail_661_);
lean_dec_ref(v_t_623_);
v___x_662_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_660_, v_init_624_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
if (lean_obj_tag(v___x_662_) == 0)
{
lean_object* v_a_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v_a_663_ = lean_ctor_get(v___x_662_, 0);
lean_inc(v_a_663_);
v___x_664_ = lean_array_get_size(v_tail_661_);
v___x_665_ = lean_nat_dec_lt(v___x_638_, v___x_664_);
if (v___x_665_ == 0)
{
lean_dec(v_a_663_);
lean_dec_ref(v_tail_661_);
return v___x_662_;
}
else
{
size_t v___x_666_; size_t v___x_667_; lean_object* v___x_668_; 
lean_dec_ref_known(v___x_662_, 1);
v___x_666_ = ((size_t)0ULL);
v___x_667_ = lean_usize_of_nat(v___x_664_);
v___x_668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_661_, v___x_666_, v___x_667_, v_a_663_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_tail_661_);
return v___x_668_;
}
}
else
{
lean_dec_ref(v_tail_661_);
return v___x_662_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object* v_t_669_, lean_object* v_init_670_, lean_object* v_start_671_, lean_object* v___y_672_, lean_object* v___y_673_, lean_object* v___y_674_, lean_object* v___y_675_, lean_object* v___y_676_, lean_object* v___y_677_, lean_object* v___y_678_, lean_object* v___y_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_){
_start:
{
lean_object* v_res_684_; 
v_res_684_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_669_, v_init_670_, v_start_671_, v___y_672_, v___y_673_, v___y_674_, v___y_675_, v___y_676_, v___y_677_, v___y_678_, v___y_679_, v___y_680_, v___y_681_, v___y_682_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v___y_680_);
lean_dec_ref(v___y_679_);
lean_dec(v___y_678_);
lean_dec_ref(v___y_677_);
lean_dec(v___y_676_);
lean_dec_ref(v___y_675_);
lean_dec(v___y_674_);
lean_dec(v___y_673_);
lean_dec_ref(v___y_672_);
lean_dec(v_start_671_);
return v_res_684_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(lean_object* v_lctx_685_, lean_object* v_init_686_, lean_object* v_start_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_, lean_object* v___y_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_){
_start:
{
lean_object* v_decls_700_; lean_object* v___x_701_; 
v_decls_700_ = lean_ctor_get(v_lctx_685_, 1);
lean_inc_ref(v_decls_700_);
lean_dec_ref(v_lctx_685_);
v___x_701_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_700_, v_init_686_, v_start_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_, v___y_695_, v___y_696_, v___y_697_, v___y_698_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object* v_lctx_702_, lean_object* v_init_703_, lean_object* v_start_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_){
_start:
{
lean_object* v_res_717_; 
v_res_717_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_702_, v_init_703_, v_start_704_, v___y_705_, v___y_706_, v___y_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec_ref(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec(v___y_707_);
lean_dec(v___y_706_);
lean_dec_ref(v___y_705_);
lean_dec(v_start_704_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(lean_object* v_scope_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_){
_start:
{
lean_object* v_lctx_731_; lean_object* v_decls_732_; lean_object* v_nextDeclIdx_733_; lean_object* v_size_734_; uint8_t v___x_735_; 
v_lctx_731_ = lean_ctor_get(v___y_726_, 2);
v_decls_732_ = lean_ctor_get(v_lctx_731_, 1);
v_nextDeclIdx_733_ = lean_ctor_get(v_scope_718_, 3);
v_size_734_ = lean_ctor_get(v_decls_732_, 2);
v___x_735_ = lean_nat_dec_eq(v_nextDeclIdx_733_, v_size_734_);
if (v___x_735_ == 0)
{
lean_object* v___x_736_; 
lean_inc(v_nextDeclIdx_733_);
lean_inc_ref(v_lctx_731_);
v___x_736_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_731_, v_scope_718_, v_nextDeclIdx_733_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_);
lean_dec(v_nextDeclIdx_733_);
if (lean_obj_tag(v___x_736_) == 0)
{
lean_object* v_a_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_755_; 
v_a_737_ = lean_ctor_get(v___x_736_, 0);
v_isSharedCheck_755_ = !lean_is_exclusive(v___x_736_);
if (v_isSharedCheck_755_ == 0)
{
v___x_739_ = v___x_736_;
v_isShared_740_ = v_isSharedCheck_755_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_a_737_);
lean_dec(v___x_736_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_755_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v_specs_741_; lean_object* v_jps_742_; lean_object* v_lastLiftedPre_x3f_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_753_; 
v_specs_741_ = lean_ctor_get(v_a_737_, 0);
v_jps_742_ = lean_ctor_get(v_a_737_, 1);
v_lastLiftedPre_x3f_743_ = lean_ctor_get(v_a_737_, 2);
v_isSharedCheck_753_ = !lean_is_exclusive(v_a_737_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v_a_737_, 3);
lean_dec(v_unused_754_);
v___x_745_ = v_a_737_;
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_lastLiftedPre_x3f_743_);
lean_inc(v_jps_742_);
lean_inc(v_specs_741_);
lean_dec(v_a_737_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_753_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_748_; 
lean_inc(v_size_734_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 3, v_size_734_);
v___x_748_ = v___x_745_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_specs_741_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_jps_742_);
lean_ctor_set(v_reuseFailAlloc_752_, 2, v_lastLiftedPre_x3f_743_);
lean_ctor_set(v_reuseFailAlloc_752_, 3, v_size_734_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 0, v___x_748_);
v___x_750_ = v___x_739_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
else
{
return v___x_736_;
}
}
else
{
lean_object* v___x_756_; 
v___x_756_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_756_, 0, v_scope_718_);
return v___x_756_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object* v_scope_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(v_scope_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_, v___y_767_, v___y_768_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
lean_dec(v___y_766_);
lean_dec_ref(v___y_765_);
lean_dec(v___y_764_);
lean_dec_ref(v___y_763_);
lean_dec(v___y_762_);
lean_dec_ref(v___y_761_);
lean_dec(v___y_760_);
lean_dec(v___y_759_);
lean_dec_ref(v___y_758_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(lean_object* v_scope_771_, lean_object* v_goal_772_, lean_object* v_a_773_, lean_object* v_a_774_, lean_object* v_a_775_, lean_object* v_a_776_, lean_object* v_a_777_, lean_object* v_a_778_, lean_object* v_a_779_, lean_object* v_a_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_){
_start:
{
lean_object* v___f_785_; lean_object* v___x_786_; 
v___f_785_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_785_, 0, v_scope_771_);
v___x_786_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_772_, v___f_785_, v_a_773_, v_a_774_, v_a_775_, v_a_776_, v_a_777_, v_a_778_, v_a_779_, v_a_780_, v_a_781_, v_a_782_, v_a_783_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___boxed(lean_object* v_scope_787_, lean_object* v_goal_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_, lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_787_, v_goal_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_, v_a_795_, v_a_796_, v_a_797_, v_a_798_, v_a_799_);
lean_dec(v_a_799_);
lean_dec_ref(v_a_798_);
lean_dec(v_a_797_);
lean_dec_ref(v_a_796_);
lean_dec(v_a_795_);
lean_dec_ref(v_a_794_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
lean_dec(v_a_790_);
lean_dec_ref(v_a_789_);
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object* v_as_802_, size_t v_i_803_, size_t v_stop_804_, lean_object* v_b_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_){
_start:
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_802_, v_i_803_, v_stop_804_, v_b_805_, v___y_813_, v___y_814_, v___y_815_, v___y_816_);
return v___x_818_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object* v_as_819_, lean_object* v_i_820_, lean_object* v_stop_821_, lean_object* v_b_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
size_t v_i_boxed_835_; size_t v_stop_boxed_836_; lean_object* v_res_837_; 
v_i_boxed_835_ = lean_unbox_usize(v_i_820_);
lean_dec(v_i_820_);
v_stop_boxed_836_ = lean_unbox_usize(v_stop_821_);
lean_dec(v_stop_821_);
v_res_837_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_819_, v_i_boxed_835_, v_stop_boxed_836_, v_b_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v___y_825_);
lean_dec(v___y_824_);
lean_dec_ref(v___y_823_);
lean_dec_ref(v_as_819_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(lean_object* v_a_838_){
_start:
{
lean_object* v___x_840_; lean_object* v_fuel_845_; 
v___x_840_ = lean_st_ref_get(v_a_838_);
v_fuel_845_ = lean_ctor_get(v___x_840_, 8);
lean_inc(v_fuel_845_);
lean_dec(v___x_840_);
if (lean_obj_tag(v_fuel_845_) == 0)
{
lean_object* v_n_846_; lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_856_; 
v_n_846_ = lean_ctor_get(v_fuel_845_, 0);
v_isSharedCheck_856_ = !lean_is_exclusive(v_fuel_845_);
if (v_isSharedCheck_856_ == 0)
{
v___x_848_ = v_fuel_845_;
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
else
{
lean_inc(v_n_846_);
lean_dec(v_fuel_845_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_856_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = lean_unsigned_to_nat(0u);
v___x_851_ = lean_nat_dec_eq(v_n_846_, v___x_850_);
lean_dec(v_n_846_);
if (v___x_851_ == 0)
{
lean_del_object(v___x_848_);
goto v___jp_841_;
}
else
{
lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_852_ = lean_box(v___x_851_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_852_);
v___x_854_ = v___x_848_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
else
{
lean_dec(v_fuel_845_);
goto v___jp_841_;
}
v___jp_841_:
{
uint8_t v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = 0;
v___x_843_ = lean_box(v___x_842_);
v___x_844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_844_, 0, v___x_843_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg___boxed(lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_857_);
lean_dec(v_a_857_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel(lean_object* v_a_860_, lean_object* v_a_861_, lean_object* v_a_862_, lean_object* v_a_863_, lean_object* v_a_864_, lean_object* v_a_865_, lean_object* v_a_866_, lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_){
_start:
{
lean_object* v___x_872_; 
v___x_872_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_861_);
return v___x_872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___boxed(lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v_res_885_; 
v_res_885_ = l_Lean_Elab_Tactic_VCGen_outOfFuel(v_a_873_, v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_);
lean_dec(v_a_883_);
lean_dec_ref(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
lean_dec(v_a_879_);
lean_dec_ref(v_a_878_);
lean_dec(v_a_877_);
lean_dec_ref(v_a_876_);
lean_dec(v_a_875_);
lean_dec(v_a_874_);
lean_dec_ref(v_a_873_);
return v_res_885_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg(lean_object* v_a_886_){
_start:
{
lean_object* v___x_888_; lean_object* v_specBackwardRuleCache_889_; lean_object* v_splitBackwardRuleCache_890_; lean_object* v_latticeBackwardRuleCache_891_; lean_object* v_frameBackwardRuleCache_892_; lean_object* v_frameDB_893_; lean_object* v_invariants_894_; lean_object* v_vcs_895_; lean_object* v_simpState_896_; lean_object* v_fuel_897_; lean_object* v_inlineHandledInvariants_898_; lean_object* v___x_900_; uint8_t v_isShared_901_; uint8_t v_isSharedCheck_923_; 
v___x_888_ = lean_st_ref_take(v_a_886_);
v_specBackwardRuleCache_889_ = lean_ctor_get(v___x_888_, 0);
v_splitBackwardRuleCache_890_ = lean_ctor_get(v___x_888_, 1);
v_latticeBackwardRuleCache_891_ = lean_ctor_get(v___x_888_, 2);
v_frameBackwardRuleCache_892_ = lean_ctor_get(v___x_888_, 3);
v_frameDB_893_ = lean_ctor_get(v___x_888_, 4);
v_invariants_894_ = lean_ctor_get(v___x_888_, 5);
v_vcs_895_ = lean_ctor_get(v___x_888_, 6);
v_simpState_896_ = lean_ctor_get(v___x_888_, 7);
v_fuel_897_ = lean_ctor_get(v___x_888_, 8);
v_inlineHandledInvariants_898_ = lean_ctor_get(v___x_888_, 9);
v_isSharedCheck_923_ = !lean_is_exclusive(v___x_888_);
if (v_isSharedCheck_923_ == 0)
{
v___x_900_ = v___x_888_;
v_isShared_901_ = v_isSharedCheck_923_;
goto v_resetjp_899_;
}
else
{
lean_inc(v_inlineHandledInvariants_898_);
lean_inc(v_fuel_897_);
lean_inc(v_simpState_896_);
lean_inc(v_vcs_895_);
lean_inc(v_invariants_894_);
lean_inc(v_frameDB_893_);
lean_inc(v_frameBackwardRuleCache_892_);
lean_inc(v_latticeBackwardRuleCache_891_);
lean_inc(v_splitBackwardRuleCache_890_);
lean_inc(v_specBackwardRuleCache_889_);
lean_dec(v___x_888_);
v___x_900_ = lean_box(0);
v_isShared_901_ = v_isSharedCheck_923_;
goto v_resetjp_899_;
}
v_resetjp_899_:
{
lean_object* v___x_902_; lean_object* v___y_904_; 
v___x_902_ = lean_box(0);
if (lean_obj_tag(v_fuel_897_) == 0)
{
lean_object* v_n_910_; lean_object* v_zero_911_; uint8_t v_isZero_912_; 
v_n_910_ = lean_ctor_get(v_fuel_897_, 0);
v_zero_911_ = lean_unsigned_to_nat(0u);
v_isZero_912_ = lean_nat_dec_eq(v_n_910_, v_zero_911_);
if (v_isZero_912_ == 0)
{
lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_921_; 
lean_inc(v_n_910_);
v_isSharedCheck_921_ = !lean_is_exclusive(v_fuel_897_);
if (v_isSharedCheck_921_ == 0)
{
lean_object* v_unused_922_; 
v_unused_922_ = lean_ctor_get(v_fuel_897_, 0);
lean_dec(v_unused_922_);
v___x_914_ = v_fuel_897_;
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
else
{
lean_dec(v_fuel_897_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_921_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v_one_916_; lean_object* v_n_917_; lean_object* v___x_919_; 
v_one_916_ = lean_unsigned_to_nat(1u);
v_n_917_ = lean_nat_sub(v_n_910_, v_one_916_);
lean_dec(v_n_910_);
if (v_isShared_915_ == 0)
{
lean_ctor_set(v___x_914_, 0, v_n_917_);
v___x_919_ = v___x_914_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_n_917_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
v___y_904_ = v___x_919_;
goto v___jp_903_;
}
}
}
else
{
v___y_904_ = v_fuel_897_;
goto v___jp_903_;
}
}
else
{
v___y_904_ = v_fuel_897_;
goto v___jp_903_;
}
v___jp_903_:
{
lean_object* v___x_906_; 
if (v_isShared_901_ == 0)
{
lean_ctor_set(v___x_900_, 8, v___y_904_);
v___x_906_ = v___x_900_;
goto v_reusejp_905_;
}
else
{
lean_object* v_reuseFailAlloc_909_; 
v_reuseFailAlloc_909_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_909_, 0, v_specBackwardRuleCache_889_);
lean_ctor_set(v_reuseFailAlloc_909_, 1, v_splitBackwardRuleCache_890_);
lean_ctor_set(v_reuseFailAlloc_909_, 2, v_latticeBackwardRuleCache_891_);
lean_ctor_set(v_reuseFailAlloc_909_, 3, v_frameBackwardRuleCache_892_);
lean_ctor_set(v_reuseFailAlloc_909_, 4, v_frameDB_893_);
lean_ctor_set(v_reuseFailAlloc_909_, 5, v_invariants_894_);
lean_ctor_set(v_reuseFailAlloc_909_, 6, v_vcs_895_);
lean_ctor_set(v_reuseFailAlloc_909_, 7, v_simpState_896_);
lean_ctor_set(v_reuseFailAlloc_909_, 8, v___y_904_);
lean_ctor_set(v_reuseFailAlloc_909_, 9, v_inlineHandledInvariants_898_);
v___x_906_ = v_reuseFailAlloc_909_;
goto v_reusejp_905_;
}
v_reusejp_905_:
{
lean_object* v___x_907_; lean_object* v___x_908_; 
v___x_907_ = lean_st_ref_put(v_a_886_, v___x_906_);
v___x_908_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_908_, 0, v___x_902_);
return v___x_908_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg___boxed(lean_object* v_a_924_, lean_object* v_a_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_924_);
lean_dec(v_a_924_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne(lean_object* v_a_927_, lean_object* v_a_928_, lean_object* v_a_929_, lean_object* v_a_930_, lean_object* v_a_931_, lean_object* v_a_932_, lean_object* v_a_933_, lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_928_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___boxed(lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_){
_start:
{
lean_object* v_res_952_; 
v_res_952_ = l_Lean_Elab_Tactic_VCGen_burnOne(v_a_940_, v_a_941_, v_a_942_, v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_);
lean_dec(v_a_950_);
lean_dec_ref(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
lean_dec(v_a_946_);
lean_dec_ref(v_a_945_);
lean_dec(v_a_944_);
lean_dec_ref(v_a_943_);
lean_dec(v_a_942_);
lean_dec(v_a_941_);
lean_dec_ref(v_a_940_);
return v_res_952_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_SpecDB(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_VCGen_FrameProc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
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
