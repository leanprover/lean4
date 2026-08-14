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
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
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
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value),LEAN_SCALAR_PTR_LITERAL(33, 54, 193, 255, 75, 233, 191, 151)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_of_forall_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__8_value),LEAN_SCALAR_PTR_LITERAL(101, 62, 242, 60, 214, 49, 44, 186)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "le_of_imp_top_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__10_value),LEAN_SCALAR_PTR_LITERAL(93, 90, 131, 207, 158, 255, 244, 86)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ofProp_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__12_value),LEAN_SCALAR_PTR_LITERAL(170, 72, 238, 67, 89, 176, 13, 2)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "ofProp_meet_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__14_value),LEAN_SCALAR_PTR_LITERAL(26, 245, 193, 228, 204, 100, 105, 167)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "iSup_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__16_value),LEAN_SCALAR_PTR_LITERAL(199, 118, 246, 228, 14, 114, 190, 48)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "true_le_of_top_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__18_value),LEAN_SCALAR_PTR_LITERAL(246, 158, 62, 101, 253, 23, 66, 126)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "top_le_prop"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__20_value),LEAN_SCALAR_PTR_LITERAL(100, 220, 104, 174, 27, 127, 1, 211)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__22_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__4_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__24_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rel_refl"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__25_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__24_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__25_value),LEAN_SCALAR_PTR_LITERAL(114, 93, 162, 136, 122, 175, 235, 220)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "meet_top_le_of_le"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__27_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__27_value),LEAN_SCALAR_PTR_LITERAL(242, 230, 85, 150, 218, 12, 92, 28)}};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28_value;
static const lean_string_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_forall"};
static const lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__29 = (const lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__29_value;
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
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
v___x_11_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules(lean_object* v_a_87_, lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_){
_start:
{
lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_92_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__5));
v___x_93_ = lean_box(0);
v___x_94_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_92_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v_a_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v_a_95_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_a_95_);
lean_dec_ref_known(v___x_94_, 1);
v___x_96_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__9));
v___x_97_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_96_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_97_) == 0)
{
lean_object* v_a_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_a_98_ = lean_ctor_get(v___x_97_, 0);
lean_inc(v_a_98_);
lean_dec_ref_known(v___x_97_, 1);
v___x_99_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__11));
v___x_100_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_99_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_100_) == 0)
{
lean_object* v_a_101_; lean_object* v___x_102_; lean_object* v___x_103_; 
v_a_101_ = lean_ctor_get(v___x_100_, 0);
lean_inc(v_a_101_);
lean_dec_ref_known(v___x_100_, 1);
v___x_102_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__13));
v___x_103_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_102_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_103_) == 0)
{
lean_object* v_a_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v_a_104_ = lean_ctor_get(v___x_103_, 0);
lean_inc(v_a_104_);
lean_dec_ref_known(v___x_103_, 1);
v___x_105_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__15));
v___x_106_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_105_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_106_) == 0)
{
lean_object* v_a_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
v_a_107_ = lean_ctor_get(v___x_106_, 0);
lean_inc(v_a_107_);
lean_dec_ref_known(v___x_106_, 1);
v___x_108_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__17));
v___x_109_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_108_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v___x_112_; 
v_a_110_ = lean_ctor_get(v___x_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v___x_109_, 1);
v___x_111_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__19));
v___x_112_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_111_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v_a_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
v_a_113_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_a_113_);
lean_dec_ref_known(v___x_112_, 1);
v___x_114_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__21));
v___x_115_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_114_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_115_) == 0)
{
lean_object* v_a_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v_a_116_ = lean_ctor_get(v___x_115_, 0);
lean_inc(v_a_116_);
lean_dec_ref_known(v___x_115_, 1);
v___x_117_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__23));
v___x_118_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_117_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_118_) == 0)
{
lean_object* v_a_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v_a_119_ = lean_ctor_get(v___x_118_, 0);
lean_inc(v_a_119_);
lean_dec_ref_known(v___x_118_, 1);
v___x_120_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__26));
v___x_121_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_120_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_121_) == 0)
{
lean_object* v_a_122_; lean_object* v___x_123_; lean_object* v___x_124_; 
v_a_122_ = lean_ctor_get(v___x_121_, 0);
lean_inc(v_a_122_);
lean_dec_ref_known(v___x_121_, 1);
v___x_123_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__28));
v___x_124_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_123_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_124_) == 0)
{
lean_object* v_a_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v_a_125_ = lean_ctor_get(v___x_124_, 0);
lean_inc(v_a_125_);
lean_dec_ref_known(v___x_124_, 1);
v___x_126_ = ((lean_object*)(l_Lean_Elab_Tactic_VCGen_mkBackwardRules___closed__30));
v___x_127_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_126_, v___x_93_, v_a_87_, v_a_88_, v_a_89_, v_a_90_);
if (lean_obj_tag(v___x_127_) == 0)
{
lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_a_128_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_136_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_136_ == 0)
{
v___x_130_ = v___x_127_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_dec(v___x_127_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_132_, 0, v_a_95_);
lean_ctor_set(v___x_132_, 1, v_a_98_);
lean_ctor_set(v___x_132_, 2, v_a_101_);
lean_ctor_set(v___x_132_, 3, v_a_104_);
lean_ctor_set(v___x_132_, 4, v_a_107_);
lean_ctor_set(v___x_132_, 5, v_a_110_);
lean_ctor_set(v___x_132_, 6, v_a_113_);
lean_ctor_set(v___x_132_, 7, v_a_116_);
lean_ctor_set(v___x_132_, 8, v_a_119_);
lean_ctor_set(v___x_132_, 9, v_a_122_);
lean_ctor_set(v___x_132_, 10, v_a_125_);
lean_ctor_set(v___x_132_, 11, v_a_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
else
{
lean_object* v_a_137_; lean_object* v___x_139_; uint8_t v_isShared_140_; uint8_t v_isSharedCheck_144_; 
lean_dec(v_a_125_);
lean_dec(v_a_122_);
lean_dec(v_a_119_);
lean_dec(v_a_116_);
lean_dec(v_a_113_);
lean_dec(v_a_110_);
lean_dec(v_a_107_);
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_137_ = lean_ctor_get(v___x_127_, 0);
v_isSharedCheck_144_ = !lean_is_exclusive(v___x_127_);
if (v_isSharedCheck_144_ == 0)
{
v___x_139_ = v___x_127_;
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
else
{
lean_inc(v_a_137_);
lean_dec(v___x_127_);
v___x_139_ = lean_box(0);
v_isShared_140_ = v_isSharedCheck_144_;
goto v_resetjp_138_;
}
v_resetjp_138_:
{
lean_object* v___x_142_; 
if (v_isShared_140_ == 0)
{
v___x_142_ = v___x_139_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_a_137_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
}
else
{
lean_object* v_a_145_; lean_object* v___x_147_; uint8_t v_isShared_148_; uint8_t v_isSharedCheck_152_; 
lean_dec(v_a_122_);
lean_dec(v_a_119_);
lean_dec(v_a_116_);
lean_dec(v_a_113_);
lean_dec(v_a_110_);
lean_dec(v_a_107_);
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_145_ = lean_ctor_get(v___x_124_, 0);
v_isSharedCheck_152_ = !lean_is_exclusive(v___x_124_);
if (v_isSharedCheck_152_ == 0)
{
v___x_147_ = v___x_124_;
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
else
{
lean_inc(v_a_145_);
lean_dec(v___x_124_);
v___x_147_ = lean_box(0);
v_isShared_148_ = v_isSharedCheck_152_;
goto v_resetjp_146_;
}
v_resetjp_146_:
{
lean_object* v___x_150_; 
if (v_isShared_148_ == 0)
{
v___x_150_ = v___x_147_;
goto v_reusejp_149_;
}
else
{
lean_object* v_reuseFailAlloc_151_; 
v_reuseFailAlloc_151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_151_, 0, v_a_145_);
v___x_150_ = v_reuseFailAlloc_151_;
goto v_reusejp_149_;
}
v_reusejp_149_:
{
return v___x_150_;
}
}
}
}
else
{
lean_object* v_a_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_160_; 
lean_dec(v_a_119_);
lean_dec(v_a_116_);
lean_dec(v_a_113_);
lean_dec(v_a_110_);
lean_dec(v_a_107_);
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_153_ = lean_ctor_get(v___x_121_, 0);
v_isSharedCheck_160_ = !lean_is_exclusive(v___x_121_);
if (v_isSharedCheck_160_ == 0)
{
v___x_155_ = v___x_121_;
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_a_153_);
lean_dec(v___x_121_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_160_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_158_; 
if (v_isShared_156_ == 0)
{
v___x_158_ = v___x_155_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v_a_153_);
v___x_158_ = v_reuseFailAlloc_159_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
return v___x_158_;
}
}
}
}
else
{
lean_object* v_a_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_168_; 
lean_dec(v_a_116_);
lean_dec(v_a_113_);
lean_dec(v_a_110_);
lean_dec(v_a_107_);
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_161_ = lean_ctor_get(v___x_118_, 0);
v_isSharedCheck_168_ = !lean_is_exclusive(v___x_118_);
if (v_isSharedCheck_168_ == 0)
{
v___x_163_ = v___x_118_;
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_a_161_);
lean_dec(v___x_118_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_168_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_166_; 
if (v_isShared_164_ == 0)
{
v___x_166_ = v___x_163_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v_a_161_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
else
{
lean_object* v_a_169_; lean_object* v___x_171_; uint8_t v_isShared_172_; uint8_t v_isSharedCheck_176_; 
lean_dec(v_a_113_);
lean_dec(v_a_110_);
lean_dec(v_a_107_);
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_169_ = lean_ctor_get(v___x_115_, 0);
v_isSharedCheck_176_ = !lean_is_exclusive(v___x_115_);
if (v_isSharedCheck_176_ == 0)
{
v___x_171_ = v___x_115_;
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
else
{
lean_inc(v_a_169_);
lean_dec(v___x_115_);
v___x_171_ = lean_box(0);
v_isShared_172_ = v_isSharedCheck_176_;
goto v_resetjp_170_;
}
v_resetjp_170_:
{
lean_object* v___x_174_; 
if (v_isShared_172_ == 0)
{
v___x_174_ = v___x_171_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v_a_169_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
else
{
lean_object* v_a_177_; lean_object* v___x_179_; uint8_t v_isShared_180_; uint8_t v_isSharedCheck_184_; 
lean_dec(v_a_110_);
lean_dec(v_a_107_);
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_177_ = lean_ctor_get(v___x_112_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_112_);
if (v_isSharedCheck_184_ == 0)
{
v___x_179_ = v___x_112_;
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
else
{
lean_inc(v_a_177_);
lean_dec(v___x_112_);
v___x_179_ = lean_box(0);
v_isShared_180_ = v_isSharedCheck_184_;
goto v_resetjp_178_;
}
v_resetjp_178_:
{
lean_object* v___x_182_; 
if (v_isShared_180_ == 0)
{
v___x_182_ = v___x_179_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v_a_177_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec(v_a_107_);
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_185_ = lean_ctor_get(v___x_109_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_109_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_109_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_109_);
v___x_187_ = lean_box(0);
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
v_resetjp_186_:
{
lean_object* v___x_190_; 
if (v_isShared_188_ == 0)
{
v___x_190_ = v___x_187_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_a_185_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
return v___x_190_;
}
}
}
}
else
{
lean_object* v_a_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_200_; 
lean_dec(v_a_104_);
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_193_ = lean_ctor_get(v___x_106_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_106_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_106_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_106_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v___x_198_; 
if (v_isShared_196_ == 0)
{
v___x_198_ = v___x_195_;
goto v_reusejp_197_;
}
else
{
lean_object* v_reuseFailAlloc_199_; 
v_reuseFailAlloc_199_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_199_, 0, v_a_193_);
v___x_198_ = v_reuseFailAlloc_199_;
goto v_reusejp_197_;
}
v_reusejp_197_:
{
return v___x_198_;
}
}
}
}
else
{
lean_object* v_a_201_; lean_object* v___x_203_; uint8_t v_isShared_204_; uint8_t v_isSharedCheck_208_; 
lean_dec(v_a_101_);
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_201_ = lean_ctor_get(v___x_103_, 0);
v_isSharedCheck_208_ = !lean_is_exclusive(v___x_103_);
if (v_isSharedCheck_208_ == 0)
{
v___x_203_ = v___x_103_;
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
else
{
lean_inc(v_a_201_);
lean_dec(v___x_103_);
v___x_203_ = lean_box(0);
v_isShared_204_ = v_isSharedCheck_208_;
goto v_resetjp_202_;
}
v_resetjp_202_:
{
lean_object* v___x_206_; 
if (v_isShared_204_ == 0)
{
v___x_206_ = v___x_203_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_207_; 
v_reuseFailAlloc_207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_207_, 0, v_a_201_);
v___x_206_ = v_reuseFailAlloc_207_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
return v___x_206_;
}
}
}
}
else
{
lean_object* v_a_209_; lean_object* v___x_211_; uint8_t v_isShared_212_; uint8_t v_isSharedCheck_216_; 
lean_dec(v_a_98_);
lean_dec(v_a_95_);
v_a_209_ = lean_ctor_get(v___x_100_, 0);
v_isSharedCheck_216_ = !lean_is_exclusive(v___x_100_);
if (v_isSharedCheck_216_ == 0)
{
v___x_211_ = v___x_100_;
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
else
{
lean_inc(v_a_209_);
lean_dec(v___x_100_);
v___x_211_ = lean_box(0);
v_isShared_212_ = v_isSharedCheck_216_;
goto v_resetjp_210_;
}
v_resetjp_210_:
{
lean_object* v___x_214_; 
if (v_isShared_212_ == 0)
{
v___x_214_ = v___x_211_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_215_; 
v_reuseFailAlloc_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_215_, 0, v_a_209_);
v___x_214_ = v_reuseFailAlloc_215_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
return v___x_214_;
}
}
}
}
else
{
lean_object* v_a_217_; lean_object* v___x_219_; uint8_t v_isShared_220_; uint8_t v_isSharedCheck_224_; 
lean_dec(v_a_95_);
v_a_217_ = lean_ctor_get(v___x_97_, 0);
v_isSharedCheck_224_ = !lean_is_exclusive(v___x_97_);
if (v_isSharedCheck_224_ == 0)
{
v___x_219_ = v___x_97_;
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
else
{
lean_inc(v_a_217_);
lean_dec(v___x_97_);
v___x_219_ = lean_box(0);
v_isShared_220_ = v_isSharedCheck_224_;
goto v_resetjp_218_;
}
v_resetjp_218_:
{
lean_object* v___x_222_; 
if (v_isShared_220_ == 0)
{
v___x_222_ = v___x_219_;
goto v_reusejp_221_;
}
else
{
lean_object* v_reuseFailAlloc_223_; 
v_reuseFailAlloc_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_223_, 0, v_a_217_);
v___x_222_ = v_reuseFailAlloc_223_;
goto v_reusejp_221_;
}
v_reusejp_221_:
{
return v___x_222_;
}
}
}
}
else
{
lean_object* v_a_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_232_; 
v_a_225_ = lean_ctor_get(v___x_94_, 0);
v_isSharedCheck_232_ = !lean_is_exclusive(v___x_94_);
if (v_isSharedCheck_232_ == 0)
{
v___x_227_ = v___x_94_;
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_a_225_);
lean_dec(v___x_94_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_232_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
lean_object* v___x_230_; 
if (v_isShared_228_ == 0)
{
v___x_230_ = v___x_227_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_231_; 
v_reuseFailAlloc_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_231_, 0, v_a_225_);
v___x_230_ = v_reuseFailAlloc_231_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
return v___x_230_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___boxed(lean_object* v_a_233_, lean_object* v_a_234_, lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRules(v_a_233_, v_a_234_, v_a_235_, v_a_236_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
lean_dec(v_a_234_);
lean_dec_ref(v_a_233_);
return v_res_238_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0(void){
_start:
{
lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_239_ = lean_unsigned_to_nat(0u);
v___x_240_ = lean_box(0);
v___x_241_ = lean_box(1);
v___x_242_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_instInhabitedSpecTheorems_default;
v___x_243_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_243_, 0, v___x_242_);
lean_ctor_set(v___x_243_, 1, v___x_241_);
lean_ctor_set(v___x_243_, 2, v___x_240_);
lean_ctor_set(v___x_243_, 3, v___x_239_);
return v___x_243_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default(void){
_start:
{
lean_object* v___x_244_; 
v___x_244_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0, &l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0);
return v___x_244_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope(void){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default;
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_registerJP(lean_object* v_s_246_, lean_object* v_fv_247_, lean_object* v_info_248_){
_start:
{
lean_object* v_specs_249_; lean_object* v_jps_250_; lean_object* v_lastLiftedPre_x3f_251_; lean_object* v_nextDeclIdx_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_260_; 
v_specs_249_ = lean_ctor_get(v_s_246_, 0);
v_jps_250_ = lean_ctor_get(v_s_246_, 1);
v_lastLiftedPre_x3f_251_ = lean_ctor_get(v_s_246_, 2);
v_nextDeclIdx_252_ = lean_ctor_get(v_s_246_, 3);
v_isSharedCheck_260_ = !lean_is_exclusive(v_s_246_);
if (v_isSharedCheck_260_ == 0)
{
v___x_254_ = v_s_246_;
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_nextDeclIdx_252_);
lean_inc(v_lastLiftedPre_x3f_251_);
lean_inc(v_jps_250_);
lean_inc(v_specs_249_);
lean_dec(v_s_246_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_260_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; lean_object* v___x_258_; 
v___x_256_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_247_, v_info_248_, v_jps_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_256_);
v___x_258_ = v___x_254_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_specs_249_);
lean_ctor_set(v_reuseFailAlloc_259_, 1, v___x_256_);
lean_ctor_set(v_reuseFailAlloc_259_, 2, v_lastLiftedPre_x3f_251_);
lean_ctor_set(v_reuseFailAlloc_259_, 3, v_nextDeclIdx_252_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(lean_object* v_t_261_, lean_object* v_k_262_){
_start:
{
if (lean_obj_tag(v_t_261_) == 0)
{
lean_object* v_k_263_; lean_object* v_v_264_; lean_object* v_l_265_; lean_object* v_r_266_; uint8_t v___x_267_; 
v_k_263_ = lean_ctor_get(v_t_261_, 1);
v_v_264_ = lean_ctor_get(v_t_261_, 2);
v_l_265_ = lean_ctor_get(v_t_261_, 3);
v_r_266_ = lean_ctor_get(v_t_261_, 4);
v___x_267_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_262_, v_k_263_);
switch(v___x_267_)
{
case 0:
{
v_t_261_ = v_l_265_;
goto _start;
}
case 1:
{
lean_object* v___x_269_; 
lean_inc(v_v_264_);
v___x_269_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_269_, 0, v_v_264_);
return v___x_269_;
}
default: 
{
v_t_261_ = v_r_266_;
goto _start;
}
}
}
else
{
lean_object* v___x_271_; 
v___x_271_ = lean_box(0);
return v___x_271_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_272_, lean_object* v_k_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_272_, v_k_273_);
lean_dec(v_k_273_);
lean_dec(v_t_272_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f(lean_object* v_s_275_, lean_object* v_fv_276_){
_start:
{
lean_object* v_jps_277_; lean_object* v___x_278_; 
v_jps_277_ = lean_ctor_get(v_s_275_, 1);
v___x_278_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_jps_277_, v_fv_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f___boxed(lean_object* v_s_279_, lean_object* v_fv_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f(v_s_279_, v_fv_280_);
lean_dec(v_fv_280_);
lean_dec_ref(v_s_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0(lean_object* v_00_u03b4_282_, lean_object* v_t_283_, lean_object* v_k_284_){
_start:
{
lean_object* v___x_285_; 
v___x_285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_283_, v_k_284_);
return v___x_285_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_286_, lean_object* v_t_287_, lean_object* v_k_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0(v_00_u03b4_286_, v_t_287_, v_k_288_);
lean_dec(v_k_288_);
lean_dec(v_t_287_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(lean_object* v_s_290_, lean_object* v_thm_291_){
_start:
{
lean_object* v_specs_292_; lean_object* v_jps_293_; lean_object* v_lastLiftedPre_x3f_294_; lean_object* v_nextDeclIdx_295_; lean_object* v___x_297_; uint8_t v_isShared_298_; uint8_t v_isSharedCheck_303_; 
v_specs_292_ = lean_ctor_get(v_s_290_, 0);
v_jps_293_ = lean_ctor_get(v_s_290_, 1);
v_lastLiftedPre_x3f_294_ = lean_ctor_get(v_s_290_, 2);
v_nextDeclIdx_295_ = lean_ctor_get(v_s_290_, 3);
v_isSharedCheck_303_ = !lean_is_exclusive(v_s_290_);
if (v_isSharedCheck_303_ == 0)
{
v___x_297_ = v_s_290_;
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
else
{
lean_inc(v_nextDeclIdx_295_);
lean_inc(v_lastLiftedPre_x3f_294_);
lean_inc(v_jps_293_);
lean_inc(v_specs_292_);
lean_dec(v_s_290_);
v___x_297_ = lean_box(0);
v_isShared_298_ = v_isSharedCheck_303_;
goto v_resetjp_296_;
}
v_resetjp_296_:
{
lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_299_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_insert(v_specs_292_, v_thm_291_);
if (v_isShared_298_ == 0)
{
lean_ctor_set(v___x_297_, 0, v___x_299_);
v___x_301_ = v___x_297_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_302_; 
v_reuseFailAlloc_302_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_302_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_302_, 1, v_jps_293_);
lean_ctor_set(v_reuseFailAlloc_302_, 2, v_lastLiftedPre_x3f_294_);
lean_ctor_set(v_reuseFailAlloc_302_, 3, v_nextDeclIdx_295_);
v___x_301_ = v_reuseFailAlloc_302_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object* v_x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___x_317_; 
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
v___x_317_ = lean_apply_12(v_x_304_, v___y_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, lean_box(0));
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object* v_x_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_318_, v___y_319_, v___y_320_, v___y_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_);
lean_dec(v___y_325_);
lean_dec_ref(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
lean_dec(v___y_321_);
lean_dec(v___y_320_);
lean_dec_ref(v___y_319_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object* v_mvarId_332_, lean_object* v_x_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_){
_start:
{
lean_object* v___f_346_; lean_object* v___x_347_; 
lean_inc(v___y_340_);
lean_inc_ref(v___y_339_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
lean_inc(v___y_336_);
lean_inc(v___y_335_);
lean_inc_ref(v___y_334_);
v___f_346_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_346_, 0, v_x_333_);
lean_closure_set(v___f_346_, 1, v___y_334_);
lean_closure_set(v___f_346_, 2, v___y_335_);
lean_closure_set(v___f_346_, 3, v___y_336_);
lean_closure_set(v___f_346_, 4, v___y_337_);
lean_closure_set(v___f_346_, 5, v___y_338_);
lean_closure_set(v___f_346_, 6, v___y_339_);
lean_closure_set(v___f_346_, 7, v___y_340_);
v___x_347_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_332_, v___f_346_, v___y_341_, v___y_342_, v___y_343_, v___y_344_);
if (lean_obj_tag(v___x_347_) == 0)
{
return v___x_347_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
v_a_348_ = lean_ctor_get(v___x_347_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_347_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_347_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_347_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v___x_353_; 
if (v_isShared_351_ == 0)
{
v___x_353_ = v___x_350_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_354_; 
v_reuseFailAlloc_354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_354_, 0, v_a_348_);
v___x_353_ = v_reuseFailAlloc_354_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
return v___x_353_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object* v_mvarId_356_, lean_object* v_x_357_, lean_object* v___y_358_, lean_object* v___y_359_, lean_object* v___y_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_356_, v_x_357_, v___y_358_, v___y_359_, v___y_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec_ref(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
lean_dec(v___y_360_);
lean_dec(v___y_359_);
lean_dec_ref(v___y_358_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(lean_object* v_00_u03b1_371_, lean_object* v_mvarId_372_, lean_object* v_x_373_, lean_object* v___y_374_, lean_object* v___y_375_, lean_object* v___y_376_, lean_object* v___y_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_){
_start:
{
lean_object* v___x_386_; 
v___x_386_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_372_, v_x_373_, v___y_374_, v___y_375_, v___y_376_, v___y_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_);
return v___x_386_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object* v_00_u03b1_387_, lean_object* v_mvarId_388_, lean_object* v_x_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_387_, v_mvarId_388_, v_x_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_);
lean_dec(v___y_400_);
lean_dec_ref(v___y_399_);
lean_dec(v___y_398_);
lean_dec_ref(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
lean_dec(v___y_394_);
lean_dec_ref(v___y_393_);
lean_dec(v___y_392_);
lean_dec(v___y_391_);
lean_dec_ref(v___y_390_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object* v_as_403_, size_t v_i_404_, size_t v_stop_405_, lean_object* v_b_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_){
_start:
{
lean_object* v_a_413_; uint8_t v___x_417_; 
v___x_417_ = lean_usize_dec_eq(v_i_404_, v_stop_405_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; 
v___x_418_ = lean_array_uget_borrowed(v_as_403_, v_i_404_);
if (lean_obj_tag(v___x_418_) == 0)
{
v_a_413_ = v_b_406_;
goto v___jp_412_;
}
else
{
lean_object* v_val_419_; uint8_t v___x_420_; 
v_val_419_ = lean_ctor_get(v___x_418_, 0);
v___x_420_ = l_Lean_LocalDecl_isAuxDecl(v_val_419_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_421_ = l_Lean_LocalDecl_fvarId(v_val_419_);
v___x_422_ = lean_unsigned_to_nat(100u);
v___x_423_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_mkSpecTheoremFromLocal(v___x_421_, v___x_422_, v___y_407_, v___y_408_, v___y_409_, v___y_410_);
if (lean_obj_tag(v___x_423_) == 0)
{
lean_object* v_a_424_; 
v_a_424_ = lean_ctor_get(v___x_423_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v___x_423_, 1);
if (lean_obj_tag(v_a_424_) == 1)
{
lean_object* v_val_425_; lean_object* v___x_426_; 
v_val_425_ = lean_ctor_get(v_a_424_, 0);
lean_inc(v_val_425_);
lean_dec_ref_known(v_a_424_, 1);
v___x_426_ = l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(v_b_406_, v_val_425_);
v_a_413_ = v___x_426_;
goto v___jp_412_;
}
else
{
lean_dec(v_a_424_);
v_a_413_ = v_b_406_;
goto v___jp_412_;
}
}
else
{
lean_object* v_a_427_; lean_object* v___x_429_; uint8_t v_isShared_430_; uint8_t v_isSharedCheck_438_; 
v_a_427_ = lean_ctor_get(v___x_423_, 0);
v_isSharedCheck_438_ = !lean_is_exclusive(v___x_423_);
if (v_isSharedCheck_438_ == 0)
{
v___x_429_ = v___x_423_;
v_isShared_430_ = v_isSharedCheck_438_;
goto v_resetjp_428_;
}
else
{
lean_inc(v_a_427_);
lean_dec(v___x_423_);
v___x_429_ = lean_box(0);
v_isShared_430_ = v_isSharedCheck_438_;
goto v_resetjp_428_;
}
v_resetjp_428_:
{
uint8_t v___y_432_; uint8_t v___x_436_; 
v___x_436_ = l_Lean_Exception_isInterrupt(v_a_427_);
if (v___x_436_ == 0)
{
uint8_t v___x_437_; 
lean_inc(v_a_427_);
v___x_437_ = l_Lean_Exception_isRuntime(v_a_427_);
v___y_432_ = v___x_437_;
goto v___jp_431_;
}
else
{
v___y_432_ = v___x_436_;
goto v___jp_431_;
}
v___jp_431_:
{
if (v___y_432_ == 0)
{
lean_del_object(v___x_429_);
lean_dec(v_a_427_);
v_a_413_ = v_b_406_;
goto v___jp_412_;
}
else
{
lean_object* v___x_434_; 
lean_dec_ref(v_b_406_);
if (v_isShared_430_ == 0)
{
v___x_434_ = v___x_429_;
goto v_reusejp_433_;
}
else
{
lean_object* v_reuseFailAlloc_435_; 
v_reuseFailAlloc_435_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_435_, 0, v_a_427_);
v___x_434_ = v_reuseFailAlloc_435_;
goto v_reusejp_433_;
}
v_reusejp_433_:
{
return v___x_434_;
}
}
}
}
}
}
else
{
v_a_413_ = v_b_406_;
goto v___jp_412_;
}
}
}
else
{
lean_object* v___x_439_; 
v___x_439_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_439_, 0, v_b_406_);
return v___x_439_;
}
v___jp_412_:
{
size_t v___x_414_; size_t v___x_415_; 
v___x_414_ = ((size_t)1ULL);
v___x_415_ = lean_usize_add(v_i_404_, v___x_414_);
v_i_404_ = v___x_415_;
v_b_406_ = v_a_413_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_as_440_, lean_object* v_i_441_, lean_object* v_stop_442_, lean_object* v_b_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_){
_start:
{
size_t v_i_boxed_449_; size_t v_stop_boxed_450_; lean_object* v_res_451_; 
v_i_boxed_449_ = lean_unbox_usize(v_i_441_);
lean_dec(v_i_441_);
v_stop_boxed_450_ = lean_unbox_usize(v_stop_442_);
lean_dec(v_stop_442_);
v_res_451_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_440_, v_i_boxed_449_, v_stop_boxed_450_, v_b_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_);
lean_dec(v___y_447_);
lean_dec_ref(v___y_446_);
lean_dec(v___y_445_);
lean_dec_ref(v___y_444_);
lean_dec_ref(v_as_440_);
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object* v_x_452_, lean_object* v_x_453_, lean_object* v___y_454_, lean_object* v___y_455_, lean_object* v___y_456_, lean_object* v___y_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_){
_start:
{
if (lean_obj_tag(v_x_452_) == 0)
{
lean_object* v_cs_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_486_; 
v_cs_466_ = lean_ctor_get(v_x_452_, 0);
v_isSharedCheck_486_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_486_ == 0)
{
v___x_468_ = v_x_452_;
v_isShared_469_ = v_isSharedCheck_486_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_cs_466_);
lean_dec(v_x_452_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_486_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_470_ = lean_unsigned_to_nat(0u);
v___x_471_ = lean_array_get_size(v_cs_466_);
v___x_472_ = lean_nat_dec_lt(v___x_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_474_; 
lean_dec_ref(v_cs_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v_x_453_);
v___x_474_ = v___x_468_;
goto v_reusejp_473_;
}
else
{
lean_object* v_reuseFailAlloc_475_; 
v_reuseFailAlloc_475_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_475_, 0, v_x_453_);
v___x_474_ = v_reuseFailAlloc_475_;
goto v_reusejp_473_;
}
v_reusejp_473_:
{
return v___x_474_;
}
}
else
{
uint8_t v___x_476_; 
v___x_476_ = lean_nat_dec_le(v___x_471_, v___x_471_);
if (v___x_476_ == 0)
{
if (v___x_472_ == 0)
{
lean_object* v___x_478_; 
lean_dec_ref(v_cs_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 0, v_x_453_);
v___x_478_ = v___x_468_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v_x_453_);
v___x_478_ = v_reuseFailAlloc_479_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
return v___x_478_;
}
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
lean_del_object(v___x_468_);
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_471_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_466_, v___x_480_, v___x_481_, v_x_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec_ref(v_cs_466_);
return v___x_482_;
}
}
else
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
lean_del_object(v___x_468_);
v___x_483_ = ((size_t)0ULL);
v___x_484_ = lean_usize_of_nat(v___x_471_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_466_, v___x_483_, v___x_484_, v_x_453_, v___y_454_, v___y_455_, v___y_456_, v___y_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec_ref(v_cs_466_);
return v___x_485_;
}
}
}
}
else
{
lean_object* v_vs_487_; lean_object* v___x_489_; uint8_t v_isShared_490_; uint8_t v_isSharedCheck_507_; 
v_vs_487_ = lean_ctor_get(v_x_452_, 0);
v_isSharedCheck_507_ = !lean_is_exclusive(v_x_452_);
if (v_isSharedCheck_507_ == 0)
{
v___x_489_ = v_x_452_;
v_isShared_490_ = v_isSharedCheck_507_;
goto v_resetjp_488_;
}
else
{
lean_inc(v_vs_487_);
lean_dec(v_x_452_);
v___x_489_ = lean_box(0);
v_isShared_490_ = v_isSharedCheck_507_;
goto v_resetjp_488_;
}
v_resetjp_488_:
{
lean_object* v___x_491_; lean_object* v___x_492_; uint8_t v___x_493_; 
v___x_491_ = lean_unsigned_to_nat(0u);
v___x_492_ = lean_array_get_size(v_vs_487_);
v___x_493_ = lean_nat_dec_lt(v___x_491_, v___x_492_);
if (v___x_493_ == 0)
{
lean_object* v___x_495_; 
lean_dec_ref(v_vs_487_);
if (v_isShared_490_ == 0)
{
lean_ctor_set_tag(v___x_489_, 0);
lean_ctor_set(v___x_489_, 0, v_x_453_);
v___x_495_ = v___x_489_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v_x_453_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
else
{
uint8_t v___x_497_; 
v___x_497_ = lean_nat_dec_le(v___x_492_, v___x_492_);
if (v___x_497_ == 0)
{
if (v___x_493_ == 0)
{
lean_object* v___x_499_; 
lean_dec_ref(v_vs_487_);
if (v_isShared_490_ == 0)
{
lean_ctor_set_tag(v___x_489_, 0);
lean_ctor_set(v___x_489_, 0, v_x_453_);
v___x_499_ = v___x_489_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_500_; 
v_reuseFailAlloc_500_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_500_, 0, v_x_453_);
v___x_499_ = v_reuseFailAlloc_500_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
return v___x_499_;
}
}
else
{
size_t v___x_501_; size_t v___x_502_; lean_object* v___x_503_; 
lean_del_object(v___x_489_);
v___x_501_ = ((size_t)0ULL);
v___x_502_ = lean_usize_of_nat(v___x_492_);
v___x_503_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_487_, v___x_501_, v___x_502_, v_x_453_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec_ref(v_vs_487_);
return v___x_503_;
}
}
else
{
size_t v___x_504_; size_t v___x_505_; lean_object* v___x_506_; 
lean_del_object(v___x_489_);
v___x_504_ = ((size_t)0ULL);
v___x_505_ = lean_usize_of_nat(v___x_492_);
v___x_506_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_487_, v___x_504_, v___x_505_, v_x_453_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec_ref(v_vs_487_);
return v___x_506_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_508_, size_t v_i_509_, size_t v_stop_510_, lean_object* v_b_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_, lean_object* v___y_519_, lean_object* v___y_520_, lean_object* v___y_521_, lean_object* v___y_522_){
_start:
{
uint8_t v___x_524_; 
v___x_524_ = lean_usize_dec_eq(v_i_509_, v_stop_510_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = lean_array_uget_borrowed(v_as_508_, v_i_509_);
lean_inc(v___x_525_);
v___x_526_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_525_, v_b_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_, v___y_518_, v___y_519_, v___y_520_, v___y_521_, v___y_522_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v_a_527_; size_t v___x_528_; size_t v___x_529_; 
v_a_527_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_a_527_);
lean_dec_ref_known(v___x_526_, 1);
v___x_528_ = ((size_t)1ULL);
v___x_529_ = lean_usize_add(v_i_509_, v___x_528_);
v_i_509_ = v___x_529_;
v_b_511_ = v_a_527_;
goto _start;
}
else
{
return v___x_526_;
}
}
else
{
lean_object* v___x_531_; 
v___x_531_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_531_, 0, v_b_511_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_532_, lean_object* v_i_533_, lean_object* v_stop_534_, lean_object* v_b_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_){
_start:
{
size_t v_i_boxed_548_; size_t v_stop_boxed_549_; lean_object* v_res_550_; 
v_i_boxed_548_ = lean_unbox_usize(v_i_533_);
lean_dec(v_i_533_);
v_stop_boxed_549_ = lean_unbox_usize(v_stop_534_);
lean_dec(v_stop_534_);
v_res_550_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_532_, v_i_boxed_548_, v_stop_boxed_549_, v_b_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_);
lean_dec(v___y_546_);
lean_dec_ref(v___y_545_);
lean_dec(v___y_544_);
lean_dec_ref(v___y_543_);
lean_dec(v___y_542_);
lean_dec_ref(v___y_541_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec(v___y_537_);
lean_dec_ref(v___y_536_);
lean_dec_ref(v_as_532_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object* v_x_551_, lean_object* v_x_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_, lean_object* v___y_559_, lean_object* v___y_560_, lean_object* v___y_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_551_, v_x_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_, v___y_558_, v___y_559_, v___y_560_, v___y_561_, v___y_562_, v___y_563_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
lean_dec(v___y_561_);
lean_dec_ref(v___y_560_);
lean_dec(v___y_559_);
lean_dec_ref(v___y_558_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec(v___y_554_);
lean_dec_ref(v___y_553_);
return v_res_565_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_566_; 
v___x_566_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_566_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object* v_x_567_, size_t v_x_568_, size_t v_x_569_, lean_object* v_x_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_, lean_object* v___y_576_, lean_object* v___y_577_, lean_object* v___y_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_){
_start:
{
if (lean_obj_tag(v_x_567_) == 0)
{
lean_object* v_cs_583_; lean_object* v___x_584_; size_t v___x_585_; lean_object* v_j_586_; lean_object* v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v___x_590_; size_t v___x_591_; size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
v_cs_583_ = lean_ctor_get(v_x_567_, 0);
lean_inc_ref(v_cs_583_);
lean_dec_ref_known(v_x_567_, 1);
v___x_584_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
v___x_585_ = lean_usize_shift_right(v_x_568_, v_x_569_);
v_j_586_ = lean_usize_to_nat(v___x_585_);
v___x_587_ = lean_array_get_borrowed(v___x_584_, v_cs_583_, v_j_586_);
v___x_588_ = ((size_t)1ULL);
v___x_589_ = lean_usize_shift_left(v___x_588_, v_x_569_);
v___x_590_ = lean_usize_sub(v___x_589_, v___x_588_);
v___x_591_ = lean_usize_land(v_x_568_, v___x_590_);
v___x_592_ = ((size_t)5ULL);
v___x_593_ = lean_usize_sub(v_x_569_, v___x_592_);
lean_inc(v___x_587_);
v___x_594_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_587_, v___x_591_, v___x_593_, v_x_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
if (lean_obj_tag(v___x_594_) == 0)
{
lean_object* v_a_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; uint8_t v___x_599_; 
v_a_595_ = lean_ctor_get(v___x_594_, 0);
lean_inc(v_a_595_);
v___x_596_ = lean_unsigned_to_nat(1u);
v___x_597_ = lean_nat_add(v_j_586_, v___x_596_);
lean_dec(v_j_586_);
v___x_598_ = lean_array_get_size(v_cs_583_);
v___x_599_ = lean_nat_dec_lt(v___x_597_, v___x_598_);
if (v___x_599_ == 0)
{
lean_dec(v___x_597_);
lean_dec(v_a_595_);
lean_dec_ref(v_cs_583_);
return v___x_594_;
}
else
{
uint8_t v___x_600_; 
v___x_600_ = lean_nat_dec_le(v___x_598_, v___x_598_);
if (v___x_600_ == 0)
{
if (v___x_599_ == 0)
{
lean_dec(v___x_597_);
lean_dec(v_a_595_);
lean_dec_ref(v_cs_583_);
return v___x_594_;
}
else
{
size_t v___x_601_; size_t v___x_602_; lean_object* v___x_603_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_601_ = lean_usize_of_nat(v___x_597_);
lean_dec(v___x_597_);
v___x_602_ = lean_usize_of_nat(v___x_598_);
v___x_603_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_583_, v___x_601_, v___x_602_, v_a_595_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec_ref(v_cs_583_);
return v___x_603_;
}
}
else
{
size_t v___x_604_; size_t v___x_605_; lean_object* v___x_606_; 
lean_dec_ref_known(v___x_594_, 1);
v___x_604_ = lean_usize_of_nat(v___x_597_);
lean_dec(v___x_597_);
v___x_605_ = lean_usize_of_nat(v___x_598_);
v___x_606_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_583_, v___x_604_, v___x_605_, v_a_595_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_, v___y_576_, v___y_577_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec_ref(v_cs_583_);
return v___x_606_;
}
}
}
else
{
lean_dec(v_j_586_);
lean_dec_ref(v_cs_583_);
return v___x_594_;
}
}
else
{
lean_object* v_vs_607_; lean_object* v___x_609_; uint8_t v_isShared_610_; uint8_t v_isSharedCheck_627_; 
v_vs_607_ = lean_ctor_get(v_x_567_, 0);
v_isSharedCheck_627_ = !lean_is_exclusive(v_x_567_);
if (v_isSharedCheck_627_ == 0)
{
v___x_609_ = v_x_567_;
v_isShared_610_ = v_isSharedCheck_627_;
goto v_resetjp_608_;
}
else
{
lean_inc(v_vs_607_);
lean_dec(v_x_567_);
v___x_609_ = lean_box(0);
v_isShared_610_ = v_isSharedCheck_627_;
goto v_resetjp_608_;
}
v_resetjp_608_:
{
lean_object* v___x_611_; lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_611_ = lean_usize_to_nat(v_x_568_);
v___x_612_ = lean_array_get_size(v_vs_607_);
v___x_613_ = lean_nat_dec_lt(v___x_611_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_615_; 
lean_dec(v___x_611_);
lean_dec_ref(v_vs_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 0);
lean_ctor_set(v___x_609_, 0, v_x_570_);
v___x_615_ = v___x_609_;
goto v_reusejp_614_;
}
else
{
lean_object* v_reuseFailAlloc_616_; 
v_reuseFailAlloc_616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_616_, 0, v_x_570_);
v___x_615_ = v_reuseFailAlloc_616_;
goto v_reusejp_614_;
}
v_reusejp_614_:
{
return v___x_615_;
}
}
else
{
uint8_t v___x_617_; 
v___x_617_ = lean_nat_dec_le(v___x_612_, v___x_612_);
if (v___x_617_ == 0)
{
if (v___x_613_ == 0)
{
lean_object* v___x_619_; 
lean_dec(v___x_611_);
lean_dec_ref(v_vs_607_);
if (v_isShared_610_ == 0)
{
lean_ctor_set_tag(v___x_609_, 0);
lean_ctor_set(v___x_609_, 0, v_x_570_);
v___x_619_ = v___x_609_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_620_; 
v_reuseFailAlloc_620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_620_, 0, v_x_570_);
v___x_619_ = v_reuseFailAlloc_620_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
return v___x_619_;
}
}
else
{
size_t v___x_621_; size_t v___x_622_; lean_object* v___x_623_; 
lean_del_object(v___x_609_);
v___x_621_ = lean_usize_of_nat(v___x_611_);
lean_dec(v___x_611_);
v___x_622_ = lean_usize_of_nat(v___x_612_);
v___x_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_607_, v___x_621_, v___x_622_, v_x_570_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec_ref(v_vs_607_);
return v___x_623_;
}
}
else
{
size_t v___x_624_; size_t v___x_625_; lean_object* v___x_626_; 
lean_del_object(v___x_609_);
v___x_624_ = lean_usize_of_nat(v___x_611_);
lean_dec(v___x_611_);
v___x_625_ = lean_usize_of_nat(v___x_612_);
v___x_626_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_607_, v___x_624_, v___x_625_, v_x_570_, v___y_578_, v___y_579_, v___y_580_, v___y_581_);
lean_dec_ref(v_vs_607_);
return v___x_626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_628_, lean_object* v_x_629_, lean_object* v_x_630_, lean_object* v_x_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_){
_start:
{
size_t v_x_24422__boxed_644_; size_t v_x_24423__boxed_645_; lean_object* v_res_646_; 
v_x_24422__boxed_644_ = lean_unbox_usize(v_x_629_);
lean_dec(v_x_629_);
v_x_24423__boxed_645_ = lean_unbox_usize(v_x_630_);
lean_dec(v_x_630_);
v_res_646_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_628_, v_x_24422__boxed_644_, v_x_24423__boxed_645_, v_x_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_);
lean_dec(v___y_642_);
lean_dec_ref(v___y_641_);
lean_dec(v___y_640_);
lean_dec_ref(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
lean_dec(v___y_636_);
lean_dec_ref(v___y_635_);
lean_dec(v___y_634_);
lean_dec(v___y_633_);
lean_dec_ref(v___y_632_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object* v_t_647_, lean_object* v_init_648_, lean_object* v_start_649_, lean_object* v___y_650_, lean_object* v___y_651_, lean_object* v___y_652_, lean_object* v___y_653_, lean_object* v___y_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_){
_start:
{
lean_object* v___x_662_; uint8_t v___x_663_; 
v___x_662_ = lean_unsigned_to_nat(0u);
v___x_663_ = lean_nat_dec_eq(v_start_649_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v_root_664_; lean_object* v_tail_665_; size_t v_shift_666_; lean_object* v_tailOff_667_; uint8_t v___x_668_; 
v_root_664_ = lean_ctor_get(v_t_647_, 0);
lean_inc_ref(v_root_664_);
v_tail_665_ = lean_ctor_get(v_t_647_, 1);
lean_inc_ref(v_tail_665_);
v_shift_666_ = lean_ctor_get_usize(v_t_647_, 4);
v_tailOff_667_ = lean_ctor_get(v_t_647_, 3);
lean_inc(v_tailOff_667_);
lean_dec_ref(v_t_647_);
v___x_668_ = lean_nat_dec_le(v_tailOff_667_, v_start_649_);
if (v___x_668_ == 0)
{
size_t v___x_669_; lean_object* v___x_670_; 
lean_dec(v_tailOff_667_);
v___x_669_ = lean_usize_of_nat(v_start_649_);
v___x_670_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_664_, v___x_669_, v_shift_666_, v_init_648_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
lean_inc(v_a_671_);
v___x_672_ = lean_array_get_size(v_tail_665_);
v___x_673_ = lean_nat_dec_lt(v___x_662_, v___x_672_);
if (v___x_673_ == 0)
{
lean_dec(v_a_671_);
lean_dec_ref(v_tail_665_);
return v___x_670_;
}
else
{
uint8_t v___x_674_; 
v___x_674_ = lean_nat_dec_le(v___x_672_, v___x_672_);
if (v___x_674_ == 0)
{
if (v___x_673_ == 0)
{
lean_dec(v_a_671_);
lean_dec_ref(v_tail_665_);
return v___x_670_;
}
else
{
size_t v___x_675_; size_t v___x_676_; lean_object* v___x_677_; 
lean_dec_ref_known(v___x_670_, 1);
v___x_675_ = ((size_t)0ULL);
v___x_676_ = lean_usize_of_nat(v___x_672_);
v___x_677_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_665_, v___x_675_, v___x_676_, v_a_671_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_tail_665_);
return v___x_677_;
}
}
else
{
size_t v___x_678_; size_t v___x_679_; lean_object* v___x_680_; 
lean_dec_ref_known(v___x_670_, 1);
v___x_678_ = ((size_t)0ULL);
v___x_679_ = lean_usize_of_nat(v___x_672_);
v___x_680_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_665_, v___x_678_, v___x_679_, v_a_671_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_tail_665_);
return v___x_680_;
}
}
}
else
{
lean_dec_ref(v_tail_665_);
return v___x_670_;
}
}
else
{
lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
lean_dec_ref(v_root_664_);
v___x_681_ = lean_nat_sub(v_start_649_, v_tailOff_667_);
lean_dec(v_tailOff_667_);
v___x_682_ = lean_array_get_size(v_tail_665_);
v___x_683_ = lean_nat_dec_lt(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_object* v___x_684_; 
lean_dec(v___x_681_);
lean_dec_ref(v_tail_665_);
v___x_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_684_, 0, v_init_648_);
return v___x_684_;
}
else
{
uint8_t v___x_685_; 
v___x_685_ = lean_nat_dec_le(v___x_682_, v___x_682_);
if (v___x_685_ == 0)
{
if (v___x_683_ == 0)
{
lean_object* v___x_686_; 
lean_dec(v___x_681_);
lean_dec_ref(v_tail_665_);
v___x_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_686_, 0, v_init_648_);
return v___x_686_;
}
else
{
size_t v___x_687_; size_t v___x_688_; lean_object* v___x_689_; 
v___x_687_ = lean_usize_of_nat(v___x_681_);
lean_dec(v___x_681_);
v___x_688_ = lean_usize_of_nat(v___x_682_);
v___x_689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_665_, v___x_687_, v___x_688_, v_init_648_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_tail_665_);
return v___x_689_;
}
}
else
{
size_t v___x_690_; size_t v___x_691_; lean_object* v___x_692_; 
v___x_690_ = lean_usize_of_nat(v___x_681_);
lean_dec(v___x_681_);
v___x_691_ = lean_usize_of_nat(v___x_682_);
v___x_692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_665_, v___x_690_, v___x_691_, v_init_648_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_tail_665_);
return v___x_692_;
}
}
}
}
else
{
lean_object* v_root_693_; lean_object* v_tail_694_; lean_object* v___x_695_; 
v_root_693_ = lean_ctor_get(v_t_647_, 0);
lean_inc_ref(v_root_693_);
v_tail_694_ = lean_ctor_get(v_t_647_, 1);
lean_inc_ref(v_tail_694_);
lean_dec_ref(v_t_647_);
v___x_695_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_693_, v_init_648_, v___y_650_, v___y_651_, v___y_652_, v___y_653_, v___y_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
if (lean_obj_tag(v___x_695_) == 0)
{
lean_object* v_a_696_; lean_object* v___x_697_; uint8_t v___x_698_; 
v_a_696_ = lean_ctor_get(v___x_695_, 0);
lean_inc(v_a_696_);
v___x_697_ = lean_array_get_size(v_tail_694_);
v___x_698_ = lean_nat_dec_lt(v___x_662_, v___x_697_);
if (v___x_698_ == 0)
{
lean_dec(v_a_696_);
lean_dec_ref(v_tail_694_);
return v___x_695_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = lean_nat_dec_le(v___x_697_, v___x_697_);
if (v___x_699_ == 0)
{
if (v___x_698_ == 0)
{
lean_dec(v_a_696_);
lean_dec_ref(v_tail_694_);
return v___x_695_;
}
else
{
size_t v___x_700_; size_t v___x_701_; lean_object* v___x_702_; 
lean_dec_ref_known(v___x_695_, 1);
v___x_700_ = ((size_t)0ULL);
v___x_701_ = lean_usize_of_nat(v___x_697_);
v___x_702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_694_, v___x_700_, v___x_701_, v_a_696_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_tail_694_);
return v___x_702_;
}
}
else
{
size_t v___x_703_; size_t v___x_704_; lean_object* v___x_705_; 
lean_dec_ref_known(v___x_695_, 1);
v___x_703_ = ((size_t)0ULL);
v___x_704_ = lean_usize_of_nat(v___x_697_);
v___x_705_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_694_, v___x_703_, v___x_704_, v_a_696_, v___y_657_, v___y_658_, v___y_659_, v___y_660_);
lean_dec_ref(v_tail_694_);
return v___x_705_;
}
}
}
else
{
lean_dec_ref(v_tail_694_);
return v___x_695_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object* v_t_706_, lean_object* v_init_707_, lean_object* v_start_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_706_, v_init_707_, v_start_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec_ref(v___y_714_);
lean_dec(v___y_713_);
lean_dec_ref(v___y_712_);
lean_dec(v___y_711_);
lean_dec(v___y_710_);
lean_dec_ref(v___y_709_);
lean_dec(v_start_708_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(lean_object* v_lctx_722_, lean_object* v_init_723_, lean_object* v_start_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_){
_start:
{
lean_object* v_decls_737_; lean_object* v___x_738_; 
v_decls_737_ = lean_ctor_get(v_lctx_722_, 1);
lean_inc_ref(v_decls_737_);
lean_dec_ref(v_lctx_722_);
v___x_738_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_737_, v_init_723_, v_start_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object* v_lctx_739_, lean_object* v_init_740_, lean_object* v_start_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_739_, v_init_740_, v_start_741_, v___y_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
lean_dec(v___y_746_);
lean_dec_ref(v___y_745_);
lean_dec(v___y_744_);
lean_dec(v___y_743_);
lean_dec_ref(v___y_742_);
lean_dec(v_start_741_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(lean_object* v_scope_755_, lean_object* v___y_756_, lean_object* v___y_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_, lean_object* v___y_762_, lean_object* v___y_763_, lean_object* v___y_764_, lean_object* v___y_765_, lean_object* v___y_766_){
_start:
{
lean_object* v_lctx_768_; lean_object* v_decls_769_; lean_object* v_nextDeclIdx_770_; lean_object* v_size_771_; uint8_t v___x_772_; 
v_lctx_768_ = lean_ctor_get(v___y_763_, 2);
v_decls_769_ = lean_ctor_get(v_lctx_768_, 1);
v_nextDeclIdx_770_ = lean_ctor_get(v_scope_755_, 3);
v_size_771_ = lean_ctor_get(v_decls_769_, 2);
v___x_772_ = lean_nat_dec_eq(v_nextDeclIdx_770_, v_size_771_);
if (v___x_772_ == 0)
{
lean_object* v___x_773_; 
lean_inc(v_nextDeclIdx_770_);
lean_inc_ref(v_lctx_768_);
v___x_773_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_768_, v_scope_755_, v_nextDeclIdx_770_, v___y_756_, v___y_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_, v___y_762_, v___y_763_, v___y_764_, v___y_765_, v___y_766_);
lean_dec(v_nextDeclIdx_770_);
if (lean_obj_tag(v___x_773_) == 0)
{
lean_object* v_a_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_792_; 
v_a_774_ = lean_ctor_get(v___x_773_, 0);
v_isSharedCheck_792_ = !lean_is_exclusive(v___x_773_);
if (v_isSharedCheck_792_ == 0)
{
v___x_776_ = v___x_773_;
v_isShared_777_ = v_isSharedCheck_792_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_a_774_);
lean_dec(v___x_773_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_792_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_specs_778_; lean_object* v_jps_779_; lean_object* v_lastLiftedPre_x3f_780_; lean_object* v___x_782_; uint8_t v_isShared_783_; uint8_t v_isSharedCheck_790_; 
v_specs_778_ = lean_ctor_get(v_a_774_, 0);
v_jps_779_ = lean_ctor_get(v_a_774_, 1);
v_lastLiftedPre_x3f_780_ = lean_ctor_get(v_a_774_, 2);
v_isSharedCheck_790_ = !lean_is_exclusive(v_a_774_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_a_774_, 3);
lean_dec(v_unused_791_);
v___x_782_ = v_a_774_;
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
else
{
lean_inc(v_lastLiftedPre_x3f_780_);
lean_inc(v_jps_779_);
lean_inc(v_specs_778_);
lean_dec(v_a_774_);
v___x_782_ = lean_box(0);
v_isShared_783_ = v_isSharedCheck_790_;
goto v_resetjp_781_;
}
v_resetjp_781_:
{
lean_object* v___x_785_; 
lean_inc(v_size_771_);
if (v_isShared_783_ == 0)
{
lean_ctor_set(v___x_782_, 3, v_size_771_);
v___x_785_ = v___x_782_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v_specs_778_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_jps_779_);
lean_ctor_set(v_reuseFailAlloc_789_, 2, v_lastLiftedPre_x3f_780_);
lean_ctor_set(v_reuseFailAlloc_789_, 3, v_size_771_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_785_);
v___x_787_ = v___x_776_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
else
{
return v___x_773_;
}
}
else
{
lean_object* v___x_793_; 
v___x_793_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_793_, 0, v_scope_755_);
return v___x_793_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object* v_scope_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(v_scope_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_, v___y_804_, v___y_805_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec(v___y_796_);
lean_dec_ref(v___y_795_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(lean_object* v_scope_808_, lean_object* v_goal_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_, lean_object* v_a_813_, lean_object* v_a_814_, lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v___f_822_; lean_object* v___x_823_; 
v___f_822_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_822_, 0, v_scope_808_);
v___x_823_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_809_, v___f_822_, v_a_810_, v_a_811_, v_a_812_, v_a_813_, v_a_814_, v_a_815_, v_a_816_, v_a_817_, v_a_818_, v_a_819_, v_a_820_);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___boxed(lean_object* v_scope_824_, lean_object* v_goal_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_, lean_object* v_a_829_, lean_object* v_a_830_, lean_object* v_a_831_, lean_object* v_a_832_, lean_object* v_a_833_, lean_object* v_a_834_, lean_object* v_a_835_, lean_object* v_a_836_, lean_object* v_a_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_824_, v_goal_825_, v_a_826_, v_a_827_, v_a_828_, v_a_829_, v_a_830_, v_a_831_, v_a_832_, v_a_833_, v_a_834_, v_a_835_, v_a_836_);
lean_dec(v_a_836_);
lean_dec_ref(v_a_835_);
lean_dec(v_a_834_);
lean_dec_ref(v_a_833_);
lean_dec(v_a_832_);
lean_dec_ref(v_a_831_);
lean_dec(v_a_830_);
lean_dec_ref(v_a_829_);
lean_dec(v_a_828_);
lean_dec(v_a_827_);
lean_dec_ref(v_a_826_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object* v_as_839_, size_t v_i_840_, size_t v_stop_841_, lean_object* v_b_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_){
_start:
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_839_, v_i_840_, v_stop_841_, v_b_842_, v___y_850_, v___y_851_, v___y_852_, v___y_853_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object* v_as_856_, lean_object* v_i_857_, lean_object* v_stop_858_, lean_object* v_b_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_, lean_object* v___y_864_, lean_object* v___y_865_, lean_object* v___y_866_, lean_object* v___y_867_, lean_object* v___y_868_, lean_object* v___y_869_, lean_object* v___y_870_, lean_object* v___y_871_){
_start:
{
size_t v_i_boxed_872_; size_t v_stop_boxed_873_; lean_object* v_res_874_; 
v_i_boxed_872_ = lean_unbox_usize(v_i_857_);
lean_dec(v_i_857_);
v_stop_boxed_873_ = lean_unbox_usize(v_stop_858_);
lean_dec(v_stop_858_);
v_res_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_856_, v_i_boxed_872_, v_stop_boxed_873_, v_b_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_, v___y_864_, v___y_865_, v___y_866_, v___y_867_, v___y_868_, v___y_869_, v___y_870_);
lean_dec(v___y_870_);
lean_dec_ref(v___y_869_);
lean_dec(v___y_868_);
lean_dec_ref(v___y_867_);
lean_dec(v___y_866_);
lean_dec_ref(v___y_865_);
lean_dec(v___y_864_);
lean_dec_ref(v___y_863_);
lean_dec(v___y_862_);
lean_dec(v___y_861_);
lean_dec_ref(v___y_860_);
lean_dec_ref(v_as_856_);
return v_res_874_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(lean_object* v_a_875_){
_start:
{
lean_object* v___x_877_; lean_object* v_fuel_878_; 
v___x_877_ = lean_st_ref_get(v_a_875_);
v_fuel_878_ = lean_ctor_get(v___x_877_, 8);
lean_inc(v_fuel_878_);
lean_dec(v___x_877_);
if (lean_obj_tag(v_fuel_878_) == 0)
{
lean_object* v_n_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_889_; 
v_n_879_ = lean_ctor_get(v_fuel_878_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_fuel_878_);
if (v_isSharedCheck_889_ == 0)
{
v___x_881_ = v_fuel_878_;
v_isShared_882_ = v_isSharedCheck_889_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_n_879_);
lean_dec(v_fuel_878_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_889_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_883_; uint8_t v___x_884_; lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_883_ = lean_unsigned_to_nat(0u);
v___x_884_ = lean_nat_dec_eq(v_n_879_, v___x_883_);
lean_dec(v_n_879_);
v___x_885_ = lean_box(v___x_884_);
if (v_isShared_882_ == 0)
{
lean_ctor_set(v___x_881_, 0, v___x_885_);
v___x_887_ = v___x_881_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
else
{
uint8_t v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; 
lean_dec(v_fuel_878_);
v___x_890_ = 0;
v___x_891_ = lean_box(v___x_890_);
v___x_892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_892_, 0, v___x_891_);
return v___x_892_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg___boxed(lean_object* v_a_893_, lean_object* v_a_894_){
_start:
{
lean_object* v_res_895_; 
v_res_895_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_893_);
lean_dec(v_a_893_);
return v_res_895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel(lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_, lean_object* v_a_905_, lean_object* v_a_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_897_);
return v___x_908_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___boxed(lean_object* v_a_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_Elab_Tactic_VCGen_outOfFuel(v_a_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_);
lean_dec(v_a_919_);
lean_dec_ref(v_a_918_);
lean_dec(v_a_917_);
lean_dec_ref(v_a_916_);
lean_dec(v_a_915_);
lean_dec_ref(v_a_914_);
lean_dec(v_a_913_);
lean_dec_ref(v_a_912_);
lean_dec(v_a_911_);
lean_dec(v_a_910_);
lean_dec_ref(v_a_909_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg(lean_object* v_a_922_){
_start:
{
lean_object* v___x_924_; lean_object* v_specBackwardRuleCache_925_; lean_object* v_splitBackwardRuleCache_926_; lean_object* v_latticeBackwardRuleCache_927_; lean_object* v_frameBackwardRuleCache_928_; lean_object* v_frameDB_929_; lean_object* v_invariants_930_; lean_object* v_vcs_931_; lean_object* v_simpState_932_; lean_object* v_fuel_933_; lean_object* v_inlineHandledInvariants_934_; lean_object* v___x_936_; uint8_t v_isShared_937_; uint8_t v_isSharedCheck_959_; 
v___x_924_ = lean_st_ref_take(v_a_922_);
v_specBackwardRuleCache_925_ = lean_ctor_get(v___x_924_, 0);
v_splitBackwardRuleCache_926_ = lean_ctor_get(v___x_924_, 1);
v_latticeBackwardRuleCache_927_ = lean_ctor_get(v___x_924_, 2);
v_frameBackwardRuleCache_928_ = lean_ctor_get(v___x_924_, 3);
v_frameDB_929_ = lean_ctor_get(v___x_924_, 4);
v_invariants_930_ = lean_ctor_get(v___x_924_, 5);
v_vcs_931_ = lean_ctor_get(v___x_924_, 6);
v_simpState_932_ = lean_ctor_get(v___x_924_, 7);
v_fuel_933_ = lean_ctor_get(v___x_924_, 8);
v_inlineHandledInvariants_934_ = lean_ctor_get(v___x_924_, 9);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_959_ == 0)
{
v___x_936_ = v___x_924_;
v_isShared_937_ = v_isSharedCheck_959_;
goto v_resetjp_935_;
}
else
{
lean_inc(v_inlineHandledInvariants_934_);
lean_inc(v_fuel_933_);
lean_inc(v_simpState_932_);
lean_inc(v_vcs_931_);
lean_inc(v_invariants_930_);
lean_inc(v_frameDB_929_);
lean_inc(v_frameBackwardRuleCache_928_);
lean_inc(v_latticeBackwardRuleCache_927_);
lean_inc(v_splitBackwardRuleCache_926_);
lean_inc(v_specBackwardRuleCache_925_);
lean_dec(v___x_924_);
v___x_936_ = lean_box(0);
v_isShared_937_ = v_isSharedCheck_959_;
goto v_resetjp_935_;
}
v_resetjp_935_:
{
lean_object* v___x_938_; lean_object* v___y_940_; 
v___x_938_ = lean_box(0);
if (lean_obj_tag(v_fuel_933_) == 0)
{
lean_object* v_n_946_; lean_object* v_zero_947_; uint8_t v_isZero_948_; 
v_n_946_ = lean_ctor_get(v_fuel_933_, 0);
v_zero_947_ = lean_unsigned_to_nat(0u);
v_isZero_948_ = lean_nat_dec_eq(v_n_946_, v_zero_947_);
if (v_isZero_948_ == 0)
{
lean_object* v___x_950_; uint8_t v_isShared_951_; uint8_t v_isSharedCheck_957_; 
lean_inc(v_n_946_);
v_isSharedCheck_957_ = !lean_is_exclusive(v_fuel_933_);
if (v_isSharedCheck_957_ == 0)
{
lean_object* v_unused_958_; 
v_unused_958_ = lean_ctor_get(v_fuel_933_, 0);
lean_dec(v_unused_958_);
v___x_950_ = v_fuel_933_;
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
else
{
lean_dec(v_fuel_933_);
v___x_950_ = lean_box(0);
v_isShared_951_ = v_isSharedCheck_957_;
goto v_resetjp_949_;
}
v_resetjp_949_:
{
lean_object* v_one_952_; lean_object* v_n_953_; lean_object* v___x_955_; 
v_one_952_ = lean_unsigned_to_nat(1u);
v_n_953_ = lean_nat_sub(v_n_946_, v_one_952_);
lean_dec(v_n_946_);
if (v_isShared_951_ == 0)
{
lean_ctor_set(v___x_950_, 0, v_n_953_);
v___x_955_ = v___x_950_;
goto v_reusejp_954_;
}
else
{
lean_object* v_reuseFailAlloc_956_; 
v_reuseFailAlloc_956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_956_, 0, v_n_953_);
v___x_955_ = v_reuseFailAlloc_956_;
goto v_reusejp_954_;
}
v_reusejp_954_:
{
v___y_940_ = v___x_955_;
goto v___jp_939_;
}
}
}
else
{
v___y_940_ = v_fuel_933_;
goto v___jp_939_;
}
}
else
{
v___y_940_ = v_fuel_933_;
goto v___jp_939_;
}
v___jp_939_:
{
lean_object* v___x_942_; 
if (v_isShared_937_ == 0)
{
lean_ctor_set(v___x_936_, 8, v___y_940_);
v___x_942_ = v___x_936_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_945_; 
v_reuseFailAlloc_945_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_945_, 0, v_specBackwardRuleCache_925_);
lean_ctor_set(v_reuseFailAlloc_945_, 1, v_splitBackwardRuleCache_926_);
lean_ctor_set(v_reuseFailAlloc_945_, 2, v_latticeBackwardRuleCache_927_);
lean_ctor_set(v_reuseFailAlloc_945_, 3, v_frameBackwardRuleCache_928_);
lean_ctor_set(v_reuseFailAlloc_945_, 4, v_frameDB_929_);
lean_ctor_set(v_reuseFailAlloc_945_, 5, v_invariants_930_);
lean_ctor_set(v_reuseFailAlloc_945_, 6, v_vcs_931_);
lean_ctor_set(v_reuseFailAlloc_945_, 7, v_simpState_932_);
lean_ctor_set(v_reuseFailAlloc_945_, 8, v___y_940_);
lean_ctor_set(v_reuseFailAlloc_945_, 9, v_inlineHandledInvariants_934_);
v___x_942_ = v_reuseFailAlloc_945_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
lean_object* v___x_943_; lean_object* v___x_944_; 
v___x_943_ = lean_st_ref_put(v_a_922_, v___x_942_);
v___x_944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_944_, 0, v___x_938_);
return v___x_944_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg___boxed(lean_object* v_a_960_, lean_object* v_a_961_){
_start:
{
lean_object* v_res_962_; 
v_res_962_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_960_);
lean_dec(v_a_960_);
return v_res_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne(lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_, lean_object* v_a_969_, lean_object* v_a_970_, lean_object* v_a_971_, lean_object* v_a_972_, lean_object* v_a_973_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_964_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___boxed(lean_object* v_a_976_, lean_object* v_a_977_, lean_object* v_a_978_, lean_object* v_a_979_, lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_){
_start:
{
lean_object* v_res_988_; 
v_res_988_ = l_Lean_Elab_Tactic_VCGen_burnOne(v_a_976_, v_a_977_, v_a_978_, v_a_979_, v_a_980_, v_a_981_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_);
lean_dec(v_a_986_);
lean_dec_ref(v_a_985_);
lean_dec(v_a_984_);
lean_dec_ref(v_a_983_);
lean_dec(v_a_982_);
lean_dec_ref(v_a_981_);
lean_dec(v_a_980_);
lean_dec_ref(v_a_979_);
lean_dec(v_a_978_);
lean_dec(v_a_977_);
lean_dec_ref(v_a_976_);
return v_res_988_;
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
