// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Context
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Basic public import Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB public import Lean.Elab.Tactic.Do.Internal.VCGen.FrameProc public import Lean.Meta.Sym.Apply public import Lean.Meta.Sym.Simp.DiscrTree public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Tactic.Grind.Types
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_instInhabitedPattern_default;
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
uint8_t l_Lean_LocalDecl_isAuxDecl(lean_object*);
lean_object* l_Lean_LocalDecl_fvarId(lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_instInhabitedPersistentArrayNode_default(lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__0;
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__1_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__2;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "Internal"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value),LEAN_SCALAR_PTR_LITERAL(33, 54, 193, 255, 75, 233, 191, 151)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_of_forall_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value),LEAN_SCALAR_PTR_LITERAL(101, 62, 242, 60, 214, 49, 44, 186)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "le_of_imp_top_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value),LEAN_SCALAR_PTR_LITERAL(93, 90, 131, 207, 158, 255, 244, 86)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ofProp_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value),LEAN_SCALAR_PTR_LITERAL(170, 72, 238, 67, 89, 176, 13, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "true_le_of_top_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value),LEAN_SCALAR_PTR_LITERAL(246, 158, 62, 101, 253, 23, 66, 126)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "top_le_prop"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value),LEAN_SCALAR_PTR_LITERAL(100, 220, 104, 174, 27, 127, 1, 211)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__20_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rel_refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__20_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value),LEAN_SCALAR_PTR_LITERAL(114, 93, 162, 136, 122, 175, 235, 220)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__23_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "meet_top_le_of_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__23_value),LEAN_SCALAR_PTR_LITERAL(237, 11, 99, 181, 146, 193, 255, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 44, 170, 221, 184, 131, 100)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "le_forall"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__26 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__26_value),LEAN_SCALAR_PTR_LITERAL(57, 100, 144, 90, 138, 155, 244, 133)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__27 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__27_value;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_registerJP(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1(void){
_start:
{
uint8_t v___x_3_; lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_3_ = 0;
v___x_4_ = lean_unsigned_to_nat(0u);
v___x_5_ = lean_box(0);
v___x_6_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__0));
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
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
return v___x_10_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__0(void){
_start:
{
lean_object* v___x_11_; 
v___x_11_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_11_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__2(void){
_start:
{
lean_object* v___x_14_; lean_object* v___x_15_; lean_object* v___x_16_; 
v___x_14_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__1));
v___x_15_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__0, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__0);
v___x_16_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_16_, 0, v___x_15_);
lean_ctor_set(v___x_16_, 1, v___x_14_);
return v___x_16_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB(void){
_start:
{
lean_object* v___x_17_; 
v___x_17_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__2, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__2_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB___closed__2);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(lean_object* v_a_80_, lean_object* v_a_81_, lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; 
v___x_85_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5));
v___x_86_ = lean_box(0);
v___x_87_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_85_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_87_) == 0)
{
lean_object* v_a_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v_a_88_ = lean_ctor_get(v___x_87_, 0);
lean_inc(v_a_88_);
lean_dec_ref_known(v___x_87_, 1);
v___x_89_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9));
v___x_90_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_89_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_90_) == 0)
{
lean_object* v_a_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v_a_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_a_91_);
lean_dec_ref_known(v___x_90_, 1);
v___x_92_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11));
v___x_93_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_92_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_93_) == 0)
{
lean_object* v_a_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v_a_94_ = lean_ctor_get(v___x_93_, 0);
lean_inc(v_a_94_);
lean_dec_ref_known(v___x_93_, 1);
v___x_95_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13));
v___x_96_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_95_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_96_) == 0)
{
lean_object* v_a_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
v_a_97_ = lean_ctor_get(v___x_96_, 0);
lean_inc(v_a_97_);
lean_dec_ref_known(v___x_96_, 1);
v___x_98_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15));
v___x_99_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_98_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_99_) == 0)
{
lean_object* v_a_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_a_100_ = lean_ctor_get(v___x_99_, 0);
lean_inc(v_a_100_);
lean_dec_ref_known(v___x_99_, 1);
v___x_101_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17));
v___x_102_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_101_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_102_) == 0)
{
lean_object* v_a_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v_a_103_ = lean_ctor_get(v___x_102_, 0);
lean_inc(v_a_103_);
lean_dec_ref_known(v___x_102_, 1);
v___x_104_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19));
v___x_105_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_104_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_105_) == 0)
{
lean_object* v_a_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v_a_106_ = lean_ctor_get(v___x_105_, 0);
lean_inc(v_a_106_);
lean_dec_ref_known(v___x_105_, 1);
v___x_107_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22));
v___x_108_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_107_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_108_) == 0)
{
lean_object* v_a_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v_a_109_ = lean_ctor_get(v___x_108_, 0);
lean_inc(v_a_109_);
lean_dec_ref_known(v___x_108_, 1);
v___x_110_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25));
v___x_111_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_110_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v_a_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v_a_112_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v___x_111_, 1);
v___x_113_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__27));
v___x_114_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_113_, v___x_86_, v_a_80_, v_a_81_, v_a_82_, v_a_83_);
if (lean_obj_tag(v___x_114_) == 0)
{
lean_object* v_a_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_123_; 
v_a_115_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_123_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_123_ == 0)
{
v___x_117_ = v___x_114_;
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_a_115_);
lean_dec(v___x_114_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_123_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_121_; 
v___x_119_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_119_, 0, v_a_88_);
lean_ctor_set(v___x_119_, 1, v_a_91_);
lean_ctor_set(v___x_119_, 2, v_a_94_);
lean_ctor_set(v___x_119_, 3, v_a_97_);
lean_ctor_set(v___x_119_, 4, v_a_100_);
lean_ctor_set(v___x_119_, 5, v_a_103_);
lean_ctor_set(v___x_119_, 6, v_a_106_);
lean_ctor_set(v___x_119_, 7, v_a_109_);
lean_ctor_set(v___x_119_, 8, v_a_112_);
lean_ctor_set(v___x_119_, 9, v_a_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 0, v___x_119_);
v___x_121_ = v___x_117_;
goto v_reusejp_120_;
}
else
{
lean_object* v_reuseFailAlloc_122_; 
v_reuseFailAlloc_122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_122_, 0, v___x_119_);
v___x_121_ = v_reuseFailAlloc_122_;
goto v_reusejp_120_;
}
v_reusejp_120_:
{
return v___x_121_;
}
}
}
else
{
lean_object* v_a_124_; lean_object* v___x_126_; uint8_t v_isShared_127_; uint8_t v_isSharedCheck_131_; 
lean_dec(v_a_112_);
lean_dec(v_a_109_);
lean_dec(v_a_106_);
lean_dec(v_a_103_);
lean_dec(v_a_100_);
lean_dec(v_a_97_);
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
v_a_124_ = lean_ctor_get(v___x_114_, 0);
v_isSharedCheck_131_ = !lean_is_exclusive(v___x_114_);
if (v_isSharedCheck_131_ == 0)
{
v___x_126_ = v___x_114_;
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
else
{
lean_inc(v_a_124_);
lean_dec(v___x_114_);
v___x_126_ = lean_box(0);
v_isShared_127_ = v_isSharedCheck_131_;
goto v_resetjp_125_;
}
v_resetjp_125_:
{
lean_object* v___x_129_; 
if (v_isShared_127_ == 0)
{
v___x_129_ = v___x_126_;
goto v_reusejp_128_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v_a_124_);
v___x_129_ = v_reuseFailAlloc_130_;
goto v_reusejp_128_;
}
v_reusejp_128_:
{
return v___x_129_;
}
}
}
}
else
{
lean_object* v_a_132_; lean_object* v___x_134_; uint8_t v_isShared_135_; uint8_t v_isSharedCheck_139_; 
lean_dec(v_a_109_);
lean_dec(v_a_106_);
lean_dec(v_a_103_);
lean_dec(v_a_100_);
lean_dec(v_a_97_);
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
v_a_132_ = lean_ctor_get(v___x_111_, 0);
v_isSharedCheck_139_ = !lean_is_exclusive(v___x_111_);
if (v_isSharedCheck_139_ == 0)
{
v___x_134_ = v___x_111_;
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
else
{
lean_inc(v_a_132_);
lean_dec(v___x_111_);
v___x_134_ = lean_box(0);
v_isShared_135_ = v_isSharedCheck_139_;
goto v_resetjp_133_;
}
v_resetjp_133_:
{
lean_object* v___x_137_; 
if (v_isShared_135_ == 0)
{
v___x_137_ = v___x_134_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v_a_132_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
else
{
lean_object* v_a_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_147_; 
lean_dec(v_a_106_);
lean_dec(v_a_103_);
lean_dec(v_a_100_);
lean_dec(v_a_97_);
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
v_a_140_ = lean_ctor_get(v___x_108_, 0);
v_isSharedCheck_147_ = !lean_is_exclusive(v___x_108_);
if (v_isSharedCheck_147_ == 0)
{
v___x_142_ = v___x_108_;
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_a_140_);
lean_dec(v___x_108_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_147_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_145_; 
if (v_isShared_143_ == 0)
{
v___x_145_ = v___x_142_;
goto v_reusejp_144_;
}
else
{
lean_object* v_reuseFailAlloc_146_; 
v_reuseFailAlloc_146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_146_, 0, v_a_140_);
v___x_145_ = v_reuseFailAlloc_146_;
goto v_reusejp_144_;
}
v_reusejp_144_:
{
return v___x_145_;
}
}
}
}
else
{
lean_object* v_a_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_155_; 
lean_dec(v_a_103_);
lean_dec(v_a_100_);
lean_dec(v_a_97_);
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
v_a_148_ = lean_ctor_get(v___x_105_, 0);
v_isSharedCheck_155_ = !lean_is_exclusive(v___x_105_);
if (v_isSharedCheck_155_ == 0)
{
v___x_150_ = v___x_105_;
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_a_148_);
lean_dec(v___x_105_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_155_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_153_; 
if (v_isShared_151_ == 0)
{
v___x_153_ = v___x_150_;
goto v_reusejp_152_;
}
else
{
lean_object* v_reuseFailAlloc_154_; 
v_reuseFailAlloc_154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_154_, 0, v_a_148_);
v___x_153_ = v_reuseFailAlloc_154_;
goto v_reusejp_152_;
}
v_reusejp_152_:
{
return v___x_153_;
}
}
}
}
else
{
lean_object* v_a_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_163_; 
lean_dec(v_a_100_);
lean_dec(v_a_97_);
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
v_a_156_ = lean_ctor_get(v___x_102_, 0);
v_isSharedCheck_163_ = !lean_is_exclusive(v___x_102_);
if (v_isSharedCheck_163_ == 0)
{
v___x_158_ = v___x_102_;
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_a_156_);
lean_dec(v___x_102_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_163_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_161_; 
if (v_isShared_159_ == 0)
{
v___x_161_ = v___x_158_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v_a_156_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
}
}
else
{
lean_object* v_a_164_; lean_object* v___x_166_; uint8_t v_isShared_167_; uint8_t v_isSharedCheck_171_; 
lean_dec(v_a_97_);
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
v_a_164_ = lean_ctor_get(v___x_99_, 0);
v_isSharedCheck_171_ = !lean_is_exclusive(v___x_99_);
if (v_isSharedCheck_171_ == 0)
{
v___x_166_ = v___x_99_;
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
else
{
lean_inc(v_a_164_);
lean_dec(v___x_99_);
v___x_166_ = lean_box(0);
v_isShared_167_ = v_isSharedCheck_171_;
goto v_resetjp_165_;
}
v_resetjp_165_:
{
lean_object* v___x_169_; 
if (v_isShared_167_ == 0)
{
v___x_169_ = v___x_166_;
goto v_reusejp_168_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_a_164_);
v___x_169_ = v_reuseFailAlloc_170_;
goto v_reusejp_168_;
}
v_reusejp_168_:
{
return v___x_169_;
}
}
}
}
else
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_179_; 
lean_dec(v_a_94_);
lean_dec(v_a_91_);
lean_dec(v_a_88_);
v_a_172_ = lean_ctor_get(v___x_96_, 0);
v_isSharedCheck_179_ = !lean_is_exclusive(v___x_96_);
if (v_isSharedCheck_179_ == 0)
{
v___x_174_ = v___x_96_;
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_96_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_179_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_177_; 
if (v_isShared_175_ == 0)
{
v___x_177_ = v___x_174_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_a_172_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
else
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_187_; 
lean_dec(v_a_91_);
lean_dec(v_a_88_);
v_a_180_ = lean_ctor_get(v___x_93_, 0);
v_isSharedCheck_187_ = !lean_is_exclusive(v___x_93_);
if (v_isSharedCheck_187_ == 0)
{
v___x_182_ = v___x_93_;
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_93_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_187_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_185_; 
if (v_isShared_183_ == 0)
{
v___x_185_ = v___x_182_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v_a_180_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
else
{
lean_object* v_a_188_; lean_object* v___x_190_; uint8_t v_isShared_191_; uint8_t v_isSharedCheck_195_; 
lean_dec(v_a_88_);
v_a_188_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_195_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_195_ == 0)
{
v___x_190_ = v___x_90_;
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
else
{
lean_inc(v_a_188_);
lean_dec(v___x_90_);
v___x_190_ = lean_box(0);
v_isShared_191_ = v_isSharedCheck_195_;
goto v_resetjp_189_;
}
v_resetjp_189_:
{
lean_object* v___x_193_; 
if (v_isShared_191_ == 0)
{
v___x_193_ = v___x_190_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v_a_188_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
}
else
{
lean_object* v_a_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_203_; 
v_a_196_ = lean_ctor_get(v___x_87_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v___x_87_);
if (v_isSharedCheck_203_ == 0)
{
v___x_198_ = v___x_87_;
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_a_196_);
lean_dec(v___x_87_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_203_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___x_201_; 
if (v_isShared_199_ == 0)
{
v___x_201_ = v___x_198_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v_a_196_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
return v___x_201_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___boxed(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_, lean_object* v_a_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(v_a_204_, v_a_205_, v_a_206_, v_a_207_);
lean_dec(v_a_207_);
lean_dec_ref(v_a_206_);
lean_dec(v_a_205_);
lean_dec_ref(v_a_204_);
return v_res_209_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_210_ = lean_unsigned_to_nat(0u);
v___x_211_ = lean_box(0);
v___x_212_ = lean_box(1);
v___x_213_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default;
v___x_214_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___x_212_);
lean_ctor_set(v___x_214_, 2, v___x_211_);
lean_ctor_set(v___x_214_, 3, v___x_210_);
return v___x_214_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default(void){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0);
return v___x_215_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope(void){
_start:
{
lean_object* v___x_216_; 
v___x_216_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default;
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_registerJP(lean_object* v_s_217_, lean_object* v_fv_218_, lean_object* v_info_219_){
_start:
{
lean_object* v_specs_220_; lean_object* v_jps_221_; lean_object* v_lastLiftedPre_x3f_222_; lean_object* v_nextDeclIdx_223_; lean_object* v___x_225_; uint8_t v_isShared_226_; uint8_t v_isSharedCheck_231_; 
v_specs_220_ = lean_ctor_get(v_s_217_, 0);
v_jps_221_ = lean_ctor_get(v_s_217_, 1);
v_lastLiftedPre_x3f_222_ = lean_ctor_get(v_s_217_, 2);
v_nextDeclIdx_223_ = lean_ctor_get(v_s_217_, 3);
v_isSharedCheck_231_ = !lean_is_exclusive(v_s_217_);
if (v_isSharedCheck_231_ == 0)
{
v___x_225_ = v_s_217_;
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
else
{
lean_inc(v_nextDeclIdx_223_);
lean_inc(v_lastLiftedPre_x3f_222_);
lean_inc(v_jps_221_);
lean_inc(v_specs_220_);
lean_dec(v_s_217_);
v___x_225_ = lean_box(0);
v_isShared_226_ = v_isSharedCheck_231_;
goto v_resetjp_224_;
}
v_resetjp_224_:
{
lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_227_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_218_, v_info_219_, v_jps_221_);
if (v_isShared_226_ == 0)
{
lean_ctor_set(v___x_225_, 1, v___x_227_);
v___x_229_ = v___x_225_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v_specs_220_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_227_);
lean_ctor_set(v_reuseFailAlloc_230_, 2, v_lastLiftedPre_x3f_222_);
lean_ctor_set(v_reuseFailAlloc_230_, 3, v_nextDeclIdx_223_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(lean_object* v_t_232_, lean_object* v_k_233_){
_start:
{
if (lean_obj_tag(v_t_232_) == 0)
{
lean_object* v_k_234_; lean_object* v_v_235_; lean_object* v_l_236_; lean_object* v_r_237_; uint8_t v___x_238_; 
v_k_234_ = lean_ctor_get(v_t_232_, 1);
v_v_235_ = lean_ctor_get(v_t_232_, 2);
v_l_236_ = lean_ctor_get(v_t_232_, 3);
v_r_237_ = lean_ctor_get(v_t_232_, 4);
v___x_238_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_233_, v_k_234_);
switch(v___x_238_)
{
case 0:
{
v_t_232_ = v_l_236_;
goto _start;
}
case 1:
{
lean_object* v___x_240_; 
lean_inc(v_v_235_);
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v_v_235_);
return v___x_240_;
}
default: 
{
v_t_232_ = v_r_237_;
goto _start;
}
}
}
else
{
lean_object* v___x_242_; 
v___x_242_ = lean_box(0);
return v___x_242_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_243_, lean_object* v_k_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_243_, v_k_244_);
lean_dec(v_k_244_);
lean_dec(v_t_243_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(lean_object* v_s_246_, lean_object* v_fv_247_){
_start:
{
lean_object* v_jps_248_; lean_object* v___x_249_; 
v_jps_248_ = lean_ctor_get(v_s_246_, 1);
v___x_249_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_jps_248_, v_fv_247_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f___boxed(lean_object* v_s_250_, lean_object* v_fv_251_){
_start:
{
lean_object* v_res_252_; 
v_res_252_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(v_s_250_, v_fv_251_);
lean_dec(v_fv_251_);
lean_dec_ref(v_s_250_);
return v_res_252_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(lean_object* v_00_u03b4_253_, lean_object* v_t_254_, lean_object* v_k_255_){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_254_, v_k_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_257_, lean_object* v_t_258_, lean_object* v_k_259_){
_start:
{
lean_object* v_res_260_; 
v_res_260_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(v_00_u03b4_257_, v_t_258_, v_k_259_);
lean_dec(v_k_259_);
lean_dec(v_t_258_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(lean_object* v_s_261_, lean_object* v_thm_262_){
_start:
{
lean_object* v_specs_263_; lean_object* v_jps_264_; lean_object* v_lastLiftedPre_x3f_265_; lean_object* v_nextDeclIdx_266_; lean_object* v___x_268_; uint8_t v_isShared_269_; uint8_t v_isSharedCheck_274_; 
v_specs_263_ = lean_ctor_get(v_s_261_, 0);
v_jps_264_ = lean_ctor_get(v_s_261_, 1);
v_lastLiftedPre_x3f_265_ = lean_ctor_get(v_s_261_, 2);
v_nextDeclIdx_266_ = lean_ctor_get(v_s_261_, 3);
v_isSharedCheck_274_ = !lean_is_exclusive(v_s_261_);
if (v_isSharedCheck_274_ == 0)
{
v___x_268_ = v_s_261_;
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
else
{
lean_inc(v_nextDeclIdx_266_);
lean_inc(v_lastLiftedPre_x3f_265_);
lean_inc(v_jps_264_);
lean_inc(v_specs_263_);
lean_dec(v_s_261_);
v___x_268_ = lean_box(0);
v_isShared_269_ = v_isSharedCheck_274_;
goto v_resetjp_267_;
}
v_resetjp_267_:
{
lean_object* v___x_270_; lean_object* v___x_272_; 
v___x_270_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(v_specs_263_, v_thm_262_);
if (v_isShared_269_ == 0)
{
lean_ctor_set(v___x_268_, 0, v___x_270_);
v___x_272_ = v___x_268_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_jps_264_);
lean_ctor_set(v_reuseFailAlloc_273_, 2, v_lastLiftedPre_x3f_265_);
lean_ctor_set(v_reuseFailAlloc_273_, 3, v_nextDeclIdx_266_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object* v_x_275_, lean_object* v___y_276_, lean_object* v___y_277_, lean_object* v___y_278_, lean_object* v___y_279_, lean_object* v___y_280_, lean_object* v___y_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v___x_288_; 
lean_inc(v___y_282_);
lean_inc_ref(v___y_281_);
lean_inc(v___y_280_);
lean_inc_ref(v___y_279_);
lean_inc(v___y_278_);
lean_inc(v___y_277_);
lean_inc_ref(v___y_276_);
v___x_288_ = lean_apply_12(v_x_275_, v___y_276_, v___y_277_, v___y_278_, v___y_279_, v___y_280_, v___y_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_, v___y_286_, lean_box(0));
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object* v_x_289_, lean_object* v___y_290_, lean_object* v___y_291_, lean_object* v___y_292_, lean_object* v___y_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_, lean_object* v___y_299_, lean_object* v___y_300_, lean_object* v___y_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_289_, v___y_290_, v___y_291_, v___y_292_, v___y_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_, v___y_298_, v___y_299_, v___y_300_);
lean_dec(v___y_296_);
lean_dec_ref(v___y_295_);
lean_dec(v___y_294_);
lean_dec_ref(v___y_293_);
lean_dec(v___y_292_);
lean_dec(v___y_291_);
lean_dec_ref(v___y_290_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object* v_mvarId_303_, lean_object* v_x_304_, lean_object* v___y_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_){
_start:
{
lean_object* v___f_317_; lean_object* v___x_318_; 
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc_ref(v___y_308_);
lean_inc(v___y_307_);
lean_inc(v___y_306_);
lean_inc_ref(v___y_305_);
v___f_317_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_317_, 0, v_x_304_);
lean_closure_set(v___f_317_, 1, v___y_305_);
lean_closure_set(v___f_317_, 2, v___y_306_);
lean_closure_set(v___f_317_, 3, v___y_307_);
lean_closure_set(v___f_317_, 4, v___y_308_);
lean_closure_set(v___f_317_, 5, v___y_309_);
lean_closure_set(v___f_317_, 6, v___y_310_);
lean_closure_set(v___f_317_, 7, v___y_311_);
v___x_318_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_303_, v___f_317_, v___y_312_, v___y_313_, v___y_314_, v___y_315_);
if (lean_obj_tag(v___x_318_) == 0)
{
return v___x_318_;
}
else
{
lean_object* v_a_319_; lean_object* v___x_321_; uint8_t v_isShared_322_; uint8_t v_isSharedCheck_326_; 
v_a_319_ = lean_ctor_get(v___x_318_, 0);
v_isSharedCheck_326_ = !lean_is_exclusive(v___x_318_);
if (v_isSharedCheck_326_ == 0)
{
v___x_321_ = v___x_318_;
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
else
{
lean_inc(v_a_319_);
lean_dec(v___x_318_);
v___x_321_ = lean_box(0);
v_isShared_322_ = v_isSharedCheck_326_;
goto v_resetjp_320_;
}
v_resetjp_320_:
{
lean_object* v___x_324_; 
if (v_isShared_322_ == 0)
{
v___x_324_ = v___x_321_;
goto v_reusejp_323_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_a_319_);
v___x_324_ = v_reuseFailAlloc_325_;
goto v_reusejp_323_;
}
v_reusejp_323_:
{
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object* v_mvarId_327_, lean_object* v_x_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_, lean_object* v___y_334_, lean_object* v___y_335_, lean_object* v___y_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_327_, v_x_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_, v___y_333_, v___y_334_, v___y_335_, v___y_336_, v___y_337_, v___y_338_, v___y_339_);
lean_dec(v___y_339_);
lean_dec_ref(v___y_338_);
lean_dec(v___y_337_);
lean_dec_ref(v___y_336_);
lean_dec(v___y_335_);
lean_dec_ref(v___y_334_);
lean_dec(v___y_333_);
lean_dec_ref(v___y_332_);
lean_dec(v___y_331_);
lean_dec(v___y_330_);
lean_dec_ref(v___y_329_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(lean_object* v_00_u03b1_342_, lean_object* v_mvarId_343_, lean_object* v_x_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_, lean_object* v___y_348_, lean_object* v___y_349_, lean_object* v___y_350_, lean_object* v___y_351_, lean_object* v___y_352_, lean_object* v___y_353_, lean_object* v___y_354_, lean_object* v___y_355_){
_start:
{
lean_object* v___x_357_; 
v___x_357_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_343_, v_x_344_, v___y_345_, v___y_346_, v___y_347_, v___y_348_, v___y_349_, v___y_350_, v___y_351_, v___y_352_, v___y_353_, v___y_354_, v___y_355_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object* v_00_u03b1_358_, lean_object* v_mvarId_359_, lean_object* v_x_360_, lean_object* v___y_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_358_, v_mvarId_359_, v_x_360_, v___y_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_);
lean_dec(v___y_371_);
lean_dec_ref(v___y_370_);
lean_dec(v___y_369_);
lean_dec_ref(v___y_368_);
lean_dec(v___y_367_);
lean_dec_ref(v___y_366_);
lean_dec(v___y_365_);
lean_dec_ref(v___y_364_);
lean_dec(v___y_363_);
lean_dec(v___y_362_);
lean_dec_ref(v___y_361_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object* v_as_374_, size_t v_i_375_, size_t v_stop_376_, lean_object* v_b_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_){
_start:
{
lean_object* v_a_384_; uint8_t v___x_388_; 
v___x_388_ = lean_usize_dec_eq(v_i_375_, v_stop_376_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; 
v___x_389_ = lean_array_uget_borrowed(v_as_374_, v_i_375_);
if (lean_obj_tag(v___x_389_) == 0)
{
v_a_384_ = v_b_377_;
goto v___jp_383_;
}
else
{
lean_object* v_val_390_; uint8_t v___x_391_; 
v_val_390_ = lean_ctor_get(v___x_389_, 0);
v___x_391_ = l_Lean_LocalDecl_isAuxDecl(v_val_390_);
if (v___x_391_ == 0)
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v___x_392_ = l_Lean_LocalDecl_fvarId(v_val_390_);
v___x_393_ = lean_unsigned_to_nat(100u);
v___x_394_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(v___x_392_, v___x_393_, v___y_378_, v___y_379_, v___y_380_, v___y_381_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
if (lean_obj_tag(v_a_395_) == 1)
{
lean_object* v_val_396_; lean_object* v___x_397_; 
v_val_396_ = lean_ctor_get(v_a_395_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v_a_395_, 1);
v___x_397_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(v_b_377_, v_val_396_);
v_a_384_ = v___x_397_;
goto v___jp_383_;
}
else
{
lean_dec(v_a_395_);
v_a_384_ = v_b_377_;
goto v___jp_383_;
}
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_409_; 
v_a_398_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_409_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_409_ == 0)
{
v___x_400_ = v___x_394_;
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_409_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
uint8_t v___y_403_; uint8_t v___x_407_; 
v___x_407_ = l_Lean_Exception_isInterrupt(v_a_398_);
if (v___x_407_ == 0)
{
uint8_t v___x_408_; 
lean_inc(v_a_398_);
v___x_408_ = l_Lean_Exception_isRuntime(v_a_398_);
v___y_403_ = v___x_408_;
goto v___jp_402_;
}
else
{
v___y_403_ = v___x_407_;
goto v___jp_402_;
}
v___jp_402_:
{
if (v___y_403_ == 0)
{
lean_del_object(v___x_400_);
lean_dec(v_a_398_);
v_a_384_ = v_b_377_;
goto v___jp_383_;
}
else
{
lean_object* v___x_405_; 
lean_dec_ref(v_b_377_);
if (v_isShared_401_ == 0)
{
v___x_405_ = v___x_400_;
goto v_reusejp_404_;
}
else
{
lean_object* v_reuseFailAlloc_406_; 
v_reuseFailAlloc_406_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_406_, 0, v_a_398_);
v___x_405_ = v_reuseFailAlloc_406_;
goto v_reusejp_404_;
}
v_reusejp_404_:
{
return v___x_405_;
}
}
}
}
}
}
else
{
v_a_384_ = v_b_377_;
goto v___jp_383_;
}
}
}
else
{
lean_object* v___x_410_; 
v___x_410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_410_, 0, v_b_377_);
return v___x_410_;
}
v___jp_383_:
{
size_t v___x_385_; size_t v___x_386_; 
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_add(v_i_375_, v___x_385_);
v_i_375_ = v___x_386_;
v_b_377_ = v_a_384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_as_411_, lean_object* v_i_412_, lean_object* v_stop_413_, lean_object* v_b_414_, lean_object* v___y_415_, lean_object* v___y_416_, lean_object* v___y_417_, lean_object* v___y_418_, lean_object* v___y_419_){
_start:
{
size_t v_i_boxed_420_; size_t v_stop_boxed_421_; lean_object* v_res_422_; 
v_i_boxed_420_ = lean_unbox_usize(v_i_412_);
lean_dec(v_i_412_);
v_stop_boxed_421_ = lean_unbox_usize(v_stop_413_);
lean_dec(v_stop_413_);
v_res_422_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_411_, v_i_boxed_420_, v_stop_boxed_421_, v_b_414_, v___y_415_, v___y_416_, v___y_417_, v___y_418_);
lean_dec(v___y_418_);
lean_dec_ref(v___y_417_);
lean_dec(v___y_416_);
lean_dec_ref(v___y_415_);
lean_dec_ref(v_as_411_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object* v_x_423_, lean_object* v_x_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_, lean_object* v___y_431_, lean_object* v___y_432_, lean_object* v___y_433_, lean_object* v___y_434_, lean_object* v___y_435_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v_cs_437_; lean_object* v___x_439_; uint8_t v_isShared_440_; uint8_t v_isSharedCheck_457_; 
v_cs_437_ = lean_ctor_get(v_x_423_, 0);
v_isSharedCheck_457_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_457_ == 0)
{
v___x_439_ = v_x_423_;
v_isShared_440_ = v_isSharedCheck_457_;
goto v_resetjp_438_;
}
else
{
lean_inc(v_cs_437_);
lean_dec(v_x_423_);
v___x_439_ = lean_box(0);
v_isShared_440_ = v_isSharedCheck_457_;
goto v_resetjp_438_;
}
v_resetjp_438_:
{
lean_object* v___x_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_441_ = lean_unsigned_to_nat(0u);
v___x_442_ = lean_array_get_size(v_cs_437_);
v___x_443_ = lean_nat_dec_lt(v___x_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_445_; 
lean_dec_ref(v_cs_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_x_424_);
v___x_445_ = v___x_439_;
goto v_reusejp_444_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v_x_424_);
v___x_445_ = v_reuseFailAlloc_446_;
goto v_reusejp_444_;
}
v_reusejp_444_:
{
return v___x_445_;
}
}
else
{
uint8_t v___x_447_; 
v___x_447_ = lean_nat_dec_le(v___x_442_, v___x_442_);
if (v___x_447_ == 0)
{
if (v___x_443_ == 0)
{
lean_object* v___x_449_; 
lean_dec_ref(v_cs_437_);
if (v_isShared_440_ == 0)
{
lean_ctor_set(v___x_439_, 0, v_x_424_);
v___x_449_ = v___x_439_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_x_424_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
return v___x_449_;
}
}
else
{
size_t v___x_451_; size_t v___x_452_; lean_object* v___x_453_; 
lean_del_object(v___x_439_);
v___x_451_ = ((size_t)0ULL);
v___x_452_ = lean_usize_of_nat(v___x_442_);
v___x_453_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_437_, v___x_451_, v___x_452_, v_x_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec_ref(v_cs_437_);
return v___x_453_;
}
}
else
{
size_t v___x_454_; size_t v___x_455_; lean_object* v___x_456_; 
lean_del_object(v___x_439_);
v___x_454_ = ((size_t)0ULL);
v___x_455_ = lean_usize_of_nat(v___x_442_);
v___x_456_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_437_, v___x_454_, v___x_455_, v_x_424_, v___y_425_, v___y_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_, v___y_431_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec_ref(v_cs_437_);
return v___x_456_;
}
}
}
}
else
{
lean_object* v_vs_458_; lean_object* v___x_460_; uint8_t v_isShared_461_; uint8_t v_isSharedCheck_478_; 
v_vs_458_ = lean_ctor_get(v_x_423_, 0);
v_isSharedCheck_478_ = !lean_is_exclusive(v_x_423_);
if (v_isSharedCheck_478_ == 0)
{
v___x_460_ = v_x_423_;
v_isShared_461_ = v_isSharedCheck_478_;
goto v_resetjp_459_;
}
else
{
lean_inc(v_vs_458_);
lean_dec(v_x_423_);
v___x_460_ = lean_box(0);
v_isShared_461_ = v_isSharedCheck_478_;
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
lean_ctor_set(v___x_460_, 0, v_x_424_);
v___x_466_ = v___x_460_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_467_; 
v_reuseFailAlloc_467_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_467_, 0, v_x_424_);
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
uint8_t v___x_468_; 
v___x_468_ = lean_nat_dec_le(v___x_463_, v___x_463_);
if (v___x_468_ == 0)
{
if (v___x_464_ == 0)
{
lean_object* v___x_470_; 
lean_dec_ref(v_vs_458_);
if (v_isShared_461_ == 0)
{
lean_ctor_set_tag(v___x_460_, 0);
lean_ctor_set(v___x_460_, 0, v_x_424_);
v___x_470_ = v___x_460_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_x_424_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
return v___x_470_;
}
}
else
{
size_t v___x_472_; size_t v___x_473_; lean_object* v___x_474_; 
lean_del_object(v___x_460_);
v___x_472_ = ((size_t)0ULL);
v___x_473_ = lean_usize_of_nat(v___x_463_);
v___x_474_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_458_, v___x_472_, v___x_473_, v_x_424_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec_ref(v_vs_458_);
return v___x_474_;
}
}
else
{
size_t v___x_475_; size_t v___x_476_; lean_object* v___x_477_; 
lean_del_object(v___x_460_);
v___x_475_ = ((size_t)0ULL);
v___x_476_ = lean_usize_of_nat(v___x_463_);
v___x_477_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_458_, v___x_475_, v___x_476_, v_x_424_, v___y_432_, v___y_433_, v___y_434_, v___y_435_);
lean_dec_ref(v_vs_458_);
return v___x_477_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_479_, size_t v_i_480_, size_t v_stop_481_, lean_object* v_b_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_, lean_object* v___y_488_, lean_object* v___y_489_, lean_object* v___y_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_){
_start:
{
uint8_t v___x_495_; 
v___x_495_ = lean_usize_dec_eq(v_i_480_, v_stop_481_);
if (v___x_495_ == 0)
{
lean_object* v___x_496_; lean_object* v___x_497_; 
v___x_496_ = lean_array_uget_borrowed(v_as_479_, v_i_480_);
lean_inc(v___x_496_);
v___x_497_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_496_, v_b_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, v___y_488_, v___y_489_, v___y_490_, v___y_491_, v___y_492_, v___y_493_);
if (lean_obj_tag(v___x_497_) == 0)
{
lean_object* v_a_498_; size_t v___x_499_; size_t v___x_500_; 
v_a_498_ = lean_ctor_get(v___x_497_, 0);
lean_inc(v_a_498_);
lean_dec_ref_known(v___x_497_, 1);
v___x_499_ = ((size_t)1ULL);
v___x_500_ = lean_usize_add(v_i_480_, v___x_499_);
v_i_480_ = v___x_500_;
v_b_482_ = v_a_498_;
goto _start;
}
else
{
return v___x_497_;
}
}
else
{
lean_object* v___x_502_; 
v___x_502_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_502_, 0, v_b_482_);
return v___x_502_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_503_, lean_object* v_i_504_, lean_object* v_stop_505_, lean_object* v_b_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_, lean_object* v___y_517_, lean_object* v___y_518_){
_start:
{
size_t v_i_boxed_519_; size_t v_stop_boxed_520_; lean_object* v_res_521_; 
v_i_boxed_519_ = lean_unbox_usize(v_i_504_);
lean_dec(v_i_504_);
v_stop_boxed_520_ = lean_unbox_usize(v_stop_505_);
lean_dec(v_stop_505_);
v_res_521_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_503_, v_i_boxed_519_, v_stop_boxed_520_, v_b_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_, v___y_516_, v___y_517_);
lean_dec(v___y_517_);
lean_dec_ref(v___y_516_);
lean_dec(v___y_515_);
lean_dec_ref(v___y_514_);
lean_dec(v___y_513_);
lean_dec_ref(v___y_512_);
lean_dec(v___y_511_);
lean_dec_ref(v___y_510_);
lean_dec(v___y_509_);
lean_dec(v___y_508_);
lean_dec_ref(v___y_507_);
lean_dec_ref(v_as_503_);
return v_res_521_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object* v_x_522_, lean_object* v_x_523_, lean_object* v___y_524_, lean_object* v___y_525_, lean_object* v___y_526_, lean_object* v___y_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_522_, v_x_523_, v___y_524_, v___y_525_, v___y_526_, v___y_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec_ref(v___y_531_);
lean_dec(v___y_530_);
lean_dec_ref(v___y_529_);
lean_dec(v___y_528_);
lean_dec_ref(v___y_527_);
lean_dec(v___y_526_);
lean_dec(v___y_525_);
lean_dec_ref(v___y_524_);
return v_res_536_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_537_; 
v___x_537_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_537_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object* v_x_538_, size_t v_x_539_, size_t v_x_540_, lean_object* v_x_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
if (lean_obj_tag(v_x_538_) == 0)
{
lean_object* v_cs_554_; lean_object* v___x_555_; size_t v___x_556_; lean_object* v_j_557_; lean_object* v___x_558_; size_t v___x_559_; size_t v___x_560_; size_t v___x_561_; size_t v___x_562_; size_t v___x_563_; size_t v___x_564_; lean_object* v___x_565_; 
v_cs_554_ = lean_ctor_get(v_x_538_, 0);
lean_inc_ref(v_cs_554_);
lean_dec_ref_known(v_x_538_, 1);
v___x_555_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
v___x_556_ = lean_usize_shift_right(v_x_539_, v_x_540_);
v_j_557_ = lean_usize_to_nat(v___x_556_);
v___x_558_ = lean_array_get_borrowed(v___x_555_, v_cs_554_, v_j_557_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_shift_left(v___x_559_, v_x_540_);
v___x_561_ = lean_usize_sub(v___x_560_, v___x_559_);
v___x_562_ = lean_usize_land(v_x_539_, v___x_561_);
v___x_563_ = ((size_t)5ULL);
v___x_564_ = lean_usize_sub(v_x_540_, v___x_563_);
lean_inc(v___x_558_);
v___x_565_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_558_, v___x_562_, v___x_564_, v_x_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
if (lean_obj_tag(v___x_565_) == 0)
{
lean_object* v_a_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v_a_566_ = lean_ctor_get(v___x_565_, 0);
lean_inc(v_a_566_);
v___x_567_ = lean_unsigned_to_nat(1u);
v___x_568_ = lean_nat_add(v_j_557_, v___x_567_);
lean_dec(v_j_557_);
v___x_569_ = lean_array_get_size(v_cs_554_);
v___x_570_ = lean_nat_dec_lt(v___x_568_, v___x_569_);
if (v___x_570_ == 0)
{
lean_dec(v___x_568_);
lean_dec(v_a_566_);
lean_dec_ref(v_cs_554_);
return v___x_565_;
}
else
{
uint8_t v___x_571_; 
v___x_571_ = lean_nat_dec_le(v___x_569_, v___x_569_);
if (v___x_571_ == 0)
{
if (v___x_570_ == 0)
{
lean_dec(v___x_568_);
lean_dec(v_a_566_);
lean_dec_ref(v_cs_554_);
return v___x_565_;
}
else
{
size_t v___x_572_; size_t v___x_573_; lean_object* v___x_574_; 
lean_dec_ref_known(v___x_565_, 1);
v___x_572_ = lean_usize_of_nat(v___x_568_);
lean_dec(v___x_568_);
v___x_573_ = lean_usize_of_nat(v___x_569_);
v___x_574_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_554_, v___x_572_, v___x_573_, v_a_566_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec_ref(v_cs_554_);
return v___x_574_;
}
}
else
{
size_t v___x_575_; size_t v___x_576_; lean_object* v___x_577_; 
lean_dec_ref_known(v___x_565_, 1);
v___x_575_ = lean_usize_of_nat(v___x_568_);
lean_dec(v___x_568_);
v___x_576_ = lean_usize_of_nat(v___x_569_);
v___x_577_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_554_, v___x_575_, v___x_576_, v_a_566_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec_ref(v_cs_554_);
return v___x_577_;
}
}
}
else
{
lean_dec(v_j_557_);
lean_dec_ref(v_cs_554_);
return v___x_565_;
}
}
else
{
lean_object* v_vs_578_; lean_object* v___x_580_; uint8_t v_isShared_581_; uint8_t v_isSharedCheck_598_; 
v_vs_578_ = lean_ctor_get(v_x_538_, 0);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_538_);
if (v_isSharedCheck_598_ == 0)
{
v___x_580_ = v_x_538_;
v_isShared_581_ = v_isSharedCheck_598_;
goto v_resetjp_579_;
}
else
{
lean_inc(v_vs_578_);
lean_dec(v_x_538_);
v___x_580_ = lean_box(0);
v_isShared_581_ = v_isSharedCheck_598_;
goto v_resetjp_579_;
}
v_resetjp_579_:
{
lean_object* v___x_582_; lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_582_ = lean_usize_to_nat(v_x_539_);
v___x_583_ = lean_array_get_size(v_vs_578_);
v___x_584_ = lean_nat_dec_lt(v___x_582_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_586_; 
lean_dec(v___x_582_);
lean_dec_ref(v_vs_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 0);
lean_ctor_set(v___x_580_, 0, v_x_541_);
v___x_586_ = v___x_580_;
goto v_reusejp_585_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_x_541_);
v___x_586_ = v_reuseFailAlloc_587_;
goto v_reusejp_585_;
}
v_reusejp_585_:
{
return v___x_586_;
}
}
else
{
uint8_t v___x_588_; 
v___x_588_ = lean_nat_dec_le(v___x_583_, v___x_583_);
if (v___x_588_ == 0)
{
if (v___x_584_ == 0)
{
lean_object* v___x_590_; 
lean_dec(v___x_582_);
lean_dec_ref(v_vs_578_);
if (v_isShared_581_ == 0)
{
lean_ctor_set_tag(v___x_580_, 0);
lean_ctor_set(v___x_580_, 0, v_x_541_);
v___x_590_ = v___x_580_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_591_; 
v_reuseFailAlloc_591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_591_, 0, v_x_541_);
v___x_590_ = v_reuseFailAlloc_591_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
return v___x_590_;
}
}
else
{
size_t v___x_592_; size_t v___x_593_; lean_object* v___x_594_; 
lean_del_object(v___x_580_);
v___x_592_ = lean_usize_of_nat(v___x_582_);
lean_dec(v___x_582_);
v___x_593_ = lean_usize_of_nat(v___x_583_);
v___x_594_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_578_, v___x_592_, v___x_593_, v_x_541_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec_ref(v_vs_578_);
return v___x_594_;
}
}
else
{
size_t v___x_595_; size_t v___x_596_; lean_object* v___x_597_; 
lean_del_object(v___x_580_);
v___x_595_ = lean_usize_of_nat(v___x_582_);
lean_dec(v___x_582_);
v___x_596_ = lean_usize_of_nat(v___x_583_);
v___x_597_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_578_, v___x_595_, v___x_596_, v_x_541_, v___y_549_, v___y_550_, v___y_551_, v___y_552_);
lean_dec_ref(v_vs_578_);
return v___x_597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_599_, lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_, lean_object* v___y_607_, lean_object* v___y_608_, lean_object* v___y_609_, lean_object* v___y_610_, lean_object* v___y_611_, lean_object* v___y_612_, lean_object* v___y_613_, lean_object* v___y_614_){
_start:
{
size_t v_x_24422__boxed_615_; size_t v_x_24423__boxed_616_; lean_object* v_res_617_; 
v_x_24422__boxed_615_ = lean_unbox_usize(v_x_600_);
lean_dec(v_x_600_);
v_x_24423__boxed_616_ = lean_unbox_usize(v_x_601_);
lean_dec(v_x_601_);
v_res_617_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_599_, v_x_24422__boxed_615_, v_x_24423__boxed_616_, v_x_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_, v___y_607_, v___y_608_, v___y_609_, v___y_610_, v___y_611_, v___y_612_, v___y_613_);
lean_dec(v___y_613_);
lean_dec_ref(v___y_612_);
lean_dec(v___y_611_);
lean_dec_ref(v___y_610_);
lean_dec(v___y_609_);
lean_dec_ref(v___y_608_);
lean_dec(v___y_607_);
lean_dec_ref(v___y_606_);
lean_dec(v___y_605_);
lean_dec(v___y_604_);
lean_dec_ref(v___y_603_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object* v_t_618_, lean_object* v_init_619_, lean_object* v_start_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
lean_object* v___x_633_; uint8_t v___x_634_; 
v___x_633_ = lean_unsigned_to_nat(0u);
v___x_634_ = lean_nat_dec_eq(v_start_620_, v___x_633_);
if (v___x_634_ == 0)
{
lean_object* v_root_635_; lean_object* v_tail_636_; size_t v_shift_637_; lean_object* v_tailOff_638_; uint8_t v___x_639_; 
v_root_635_ = lean_ctor_get(v_t_618_, 0);
lean_inc_ref(v_root_635_);
v_tail_636_ = lean_ctor_get(v_t_618_, 1);
lean_inc_ref(v_tail_636_);
v_shift_637_ = lean_ctor_get_usize(v_t_618_, 4);
v_tailOff_638_ = lean_ctor_get(v_t_618_, 3);
lean_inc(v_tailOff_638_);
lean_dec_ref(v_t_618_);
v___x_639_ = lean_nat_dec_le(v_tailOff_638_, v_start_620_);
if (v___x_639_ == 0)
{
size_t v___x_640_; lean_object* v___x_641_; 
lean_dec(v_tailOff_638_);
v___x_640_ = lean_usize_of_nat(v_start_620_);
v___x_641_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_635_, v___x_640_, v_shift_637_, v_init_619_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_641_) == 0)
{
lean_object* v_a_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v_a_642_ = lean_ctor_get(v___x_641_, 0);
lean_inc(v_a_642_);
v___x_643_ = lean_array_get_size(v_tail_636_);
v___x_644_ = lean_nat_dec_lt(v___x_633_, v___x_643_);
if (v___x_644_ == 0)
{
lean_dec(v_a_642_);
lean_dec_ref(v_tail_636_);
return v___x_641_;
}
else
{
uint8_t v___x_645_; 
v___x_645_ = lean_nat_dec_le(v___x_643_, v___x_643_);
if (v___x_645_ == 0)
{
if (v___x_644_ == 0)
{
lean_dec(v_a_642_);
lean_dec_ref(v_tail_636_);
return v___x_641_;
}
else
{
size_t v___x_646_; size_t v___x_647_; lean_object* v___x_648_; 
lean_dec_ref_known(v___x_641_, 1);
v___x_646_ = ((size_t)0ULL);
v___x_647_ = lean_usize_of_nat(v___x_643_);
v___x_648_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_636_, v___x_646_, v___x_647_, v_a_642_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec_ref(v_tail_636_);
return v___x_648_;
}
}
else
{
size_t v___x_649_; size_t v___x_650_; lean_object* v___x_651_; 
lean_dec_ref_known(v___x_641_, 1);
v___x_649_ = ((size_t)0ULL);
v___x_650_ = lean_usize_of_nat(v___x_643_);
v___x_651_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_636_, v___x_649_, v___x_650_, v_a_642_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec_ref(v_tail_636_);
return v___x_651_;
}
}
}
else
{
lean_dec_ref(v_tail_636_);
return v___x_641_;
}
}
else
{
lean_object* v___x_652_; lean_object* v___x_653_; uint8_t v___x_654_; 
lean_dec_ref(v_root_635_);
v___x_652_ = lean_nat_sub(v_start_620_, v_tailOff_638_);
lean_dec(v_tailOff_638_);
v___x_653_ = lean_array_get_size(v_tail_636_);
v___x_654_ = lean_nat_dec_lt(v___x_652_, v___x_653_);
if (v___x_654_ == 0)
{
lean_object* v___x_655_; 
lean_dec(v___x_652_);
lean_dec_ref(v_tail_636_);
v___x_655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_655_, 0, v_init_619_);
return v___x_655_;
}
else
{
uint8_t v___x_656_; 
v___x_656_ = lean_nat_dec_le(v___x_653_, v___x_653_);
if (v___x_656_ == 0)
{
if (v___x_654_ == 0)
{
lean_object* v___x_657_; 
lean_dec(v___x_652_);
lean_dec_ref(v_tail_636_);
v___x_657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_657_, 0, v_init_619_);
return v___x_657_;
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
v___x_658_ = lean_usize_of_nat(v___x_652_);
lean_dec(v___x_652_);
v___x_659_ = lean_usize_of_nat(v___x_653_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_636_, v___x_658_, v___x_659_, v_init_619_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec_ref(v_tail_636_);
return v___x_660_;
}
}
else
{
size_t v___x_661_; size_t v___x_662_; lean_object* v___x_663_; 
v___x_661_ = lean_usize_of_nat(v___x_652_);
lean_dec(v___x_652_);
v___x_662_ = lean_usize_of_nat(v___x_653_);
v___x_663_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_636_, v___x_661_, v___x_662_, v_init_619_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec_ref(v_tail_636_);
return v___x_663_;
}
}
}
}
else
{
lean_object* v_root_664_; lean_object* v_tail_665_; lean_object* v___x_666_; 
v_root_664_ = lean_ctor_get(v_t_618_, 0);
lean_inc_ref(v_root_664_);
v_tail_665_ = lean_ctor_get(v_t_618_, 1);
lean_inc_ref(v_tail_665_);
lean_dec_ref(v_t_618_);
v___x_666_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_664_, v_init_619_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
if (lean_obj_tag(v___x_666_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; uint8_t v___x_669_; 
v_a_667_ = lean_ctor_get(v___x_666_, 0);
lean_inc(v_a_667_);
v___x_668_ = lean_array_get_size(v_tail_665_);
v___x_669_ = lean_nat_dec_lt(v___x_633_, v___x_668_);
if (v___x_669_ == 0)
{
lean_dec(v_a_667_);
lean_dec_ref(v_tail_665_);
return v___x_666_;
}
else
{
uint8_t v___x_670_; 
v___x_670_ = lean_nat_dec_le(v___x_668_, v___x_668_);
if (v___x_670_ == 0)
{
if (v___x_669_ == 0)
{
lean_dec(v_a_667_);
lean_dec_ref(v_tail_665_);
return v___x_666_;
}
else
{
size_t v___x_671_; size_t v___x_672_; lean_object* v___x_673_; 
lean_dec_ref_known(v___x_666_, 1);
v___x_671_ = ((size_t)0ULL);
v___x_672_ = lean_usize_of_nat(v___x_668_);
v___x_673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_665_, v___x_671_, v___x_672_, v_a_667_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec_ref(v_tail_665_);
return v___x_673_;
}
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
lean_dec_ref_known(v___x_666_, 1);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_668_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_665_, v___x_674_, v___x_675_, v_a_667_, v___y_628_, v___y_629_, v___y_630_, v___y_631_);
lean_dec_ref(v_tail_665_);
return v___x_676_;
}
}
}
else
{
lean_dec_ref(v_tail_665_);
return v___x_666_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object* v_t_677_, lean_object* v_init_678_, lean_object* v_start_679_, lean_object* v___y_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_){
_start:
{
lean_object* v_res_692_; 
v_res_692_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_677_, v_init_678_, v_start_679_, v___y_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_);
lean_dec(v___y_690_);
lean_dec_ref(v___y_689_);
lean_dec(v___y_688_);
lean_dec_ref(v___y_687_);
lean_dec(v___y_686_);
lean_dec_ref(v___y_685_);
lean_dec(v___y_684_);
lean_dec_ref(v___y_683_);
lean_dec(v___y_682_);
lean_dec(v___y_681_);
lean_dec_ref(v___y_680_);
lean_dec(v_start_679_);
return v_res_692_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(lean_object* v_lctx_693_, lean_object* v_init_694_, lean_object* v_start_695_, lean_object* v___y_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_){
_start:
{
lean_object* v_decls_708_; lean_object* v___x_709_; 
v_decls_708_ = lean_ctor_get(v_lctx_693_, 1);
lean_inc_ref(v_decls_708_);
lean_dec_ref(v_lctx_693_);
v___x_709_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_708_, v_init_694_, v_start_695_, v___y_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object* v_lctx_710_, lean_object* v_init_711_, lean_object* v_start_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_){
_start:
{
lean_object* v_res_725_; 
v_res_725_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_710_, v_init_711_, v_start_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
lean_dec(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v_start_712_);
return v_res_725_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(lean_object* v_scope_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_){
_start:
{
lean_object* v_lctx_739_; lean_object* v_decls_740_; lean_object* v_nextDeclIdx_741_; lean_object* v_size_742_; uint8_t v___x_743_; 
v_lctx_739_ = lean_ctor_get(v___y_734_, 2);
v_decls_740_ = lean_ctor_get(v_lctx_739_, 1);
v_nextDeclIdx_741_ = lean_ctor_get(v_scope_726_, 3);
v_size_742_ = lean_ctor_get(v_decls_740_, 2);
v___x_743_ = lean_nat_dec_eq(v_nextDeclIdx_741_, v_size_742_);
if (v___x_743_ == 0)
{
lean_object* v___x_744_; 
lean_inc(v_nextDeclIdx_741_);
lean_inc_ref(v_lctx_739_);
v___x_744_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_739_, v_scope_726_, v_nextDeclIdx_741_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_);
lean_dec(v_nextDeclIdx_741_);
if (lean_obj_tag(v___x_744_) == 0)
{
lean_object* v_a_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_763_; 
v_a_745_ = lean_ctor_get(v___x_744_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v___x_744_);
if (v_isSharedCheck_763_ == 0)
{
v___x_747_ = v___x_744_;
v_isShared_748_ = v_isSharedCheck_763_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_a_745_);
lean_dec(v___x_744_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_763_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_specs_749_; lean_object* v_jps_750_; lean_object* v_lastLiftedPre_x3f_751_; lean_object* v___x_753_; uint8_t v_isShared_754_; uint8_t v_isSharedCheck_761_; 
v_specs_749_ = lean_ctor_get(v_a_745_, 0);
v_jps_750_ = lean_ctor_get(v_a_745_, 1);
v_lastLiftedPre_x3f_751_ = lean_ctor_get(v_a_745_, 2);
v_isSharedCheck_761_ = !lean_is_exclusive(v_a_745_);
if (v_isSharedCheck_761_ == 0)
{
lean_object* v_unused_762_; 
v_unused_762_ = lean_ctor_get(v_a_745_, 3);
lean_dec(v_unused_762_);
v___x_753_ = v_a_745_;
v_isShared_754_ = v_isSharedCheck_761_;
goto v_resetjp_752_;
}
else
{
lean_inc(v_lastLiftedPre_x3f_751_);
lean_inc(v_jps_750_);
lean_inc(v_specs_749_);
lean_dec(v_a_745_);
v___x_753_ = lean_box(0);
v_isShared_754_ = v_isSharedCheck_761_;
goto v_resetjp_752_;
}
v_resetjp_752_:
{
lean_object* v___x_756_; 
lean_inc(v_size_742_);
if (v_isShared_754_ == 0)
{
lean_ctor_set(v___x_753_, 3, v_size_742_);
v___x_756_ = v___x_753_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_760_; 
v_reuseFailAlloc_760_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_760_, 0, v_specs_749_);
lean_ctor_set(v_reuseFailAlloc_760_, 1, v_jps_750_);
lean_ctor_set(v_reuseFailAlloc_760_, 2, v_lastLiftedPre_x3f_751_);
lean_ctor_set(v_reuseFailAlloc_760_, 3, v_size_742_);
v___x_756_ = v_reuseFailAlloc_760_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
lean_object* v___x_758_; 
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_756_);
v___x_758_ = v___x_747_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_756_);
v___x_758_ = v_reuseFailAlloc_759_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
return v___x_758_;
}
}
}
}
}
else
{
return v___x_744_;
}
}
else
{
lean_object* v___x_764_; 
v___x_764_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_764_, 0, v_scope_726_);
return v___x_764_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object* v_scope_765_, lean_object* v___y_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(v_scope_765_, v___y_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_);
lean_dec(v___y_776_);
lean_dec_ref(v___y_775_);
lean_dec(v___y_774_);
lean_dec_ref(v___y_773_);
lean_dec(v___y_772_);
lean_dec_ref(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec(v___y_767_);
lean_dec_ref(v___y_766_);
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(lean_object* v_scope_779_, lean_object* v_goal_780_, lean_object* v_a_781_, lean_object* v_a_782_, lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_){
_start:
{
lean_object* v___f_793_; lean_object* v___x_794_; 
v___f_793_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_793_, 0, v_scope_779_);
v___x_794_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_780_, v___f_793_, v_a_781_, v_a_782_, v_a_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___boxed(lean_object* v_scope_795_, lean_object* v_goal_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_){
_start:
{
lean_object* v_res_809_; 
v_res_809_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_795_, v_goal_796_, v_a_797_, v_a_798_, v_a_799_, v_a_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec_ref(v_a_802_);
lean_dec(v_a_801_);
lean_dec_ref(v_a_800_);
lean_dec(v_a_799_);
lean_dec(v_a_798_);
lean_dec_ref(v_a_797_);
return v_res_809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object* v_as_810_, size_t v_i_811_, size_t v_stop_812_, lean_object* v_b_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_){
_start:
{
lean_object* v___x_826_; 
v___x_826_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_810_, v_i_811_, v_stop_812_, v_b_813_, v___y_821_, v___y_822_, v___y_823_, v___y_824_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object* v_as_827_, lean_object* v_i_828_, lean_object* v_stop_829_, lean_object* v_b_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
size_t v_i_boxed_843_; size_t v_stop_boxed_844_; lean_object* v_res_845_; 
v_i_boxed_843_ = lean_unbox_usize(v_i_828_);
lean_dec(v_i_828_);
v_stop_boxed_844_ = lean_unbox_usize(v_stop_829_);
lean_dec(v_stop_829_);
v_res_845_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_827_, v_i_boxed_843_, v_stop_boxed_844_, v_b_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_);
lean_dec(v___y_841_);
lean_dec_ref(v___y_840_);
lean_dec(v___y_839_);
lean_dec_ref(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec(v___y_835_);
lean_dec_ref(v___y_834_);
lean_dec(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec_ref(v_as_827_);
return v_res_845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object* v_a_846_){
_start:
{
lean_object* v___x_848_; lean_object* v_fuel_849_; 
v___x_848_ = lean_st_ref_get(v_a_846_);
v_fuel_849_ = lean_ctor_get(v___x_848_, 8);
lean_inc(v_fuel_849_);
lean_dec(v___x_848_);
if (lean_obj_tag(v_fuel_849_) == 0)
{
lean_object* v_n_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_860_; 
v_n_850_ = lean_ctor_get(v_fuel_849_, 0);
v_isSharedCheck_860_ = !lean_is_exclusive(v_fuel_849_);
if (v_isSharedCheck_860_ == 0)
{
v___x_852_ = v_fuel_849_;
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_n_850_);
lean_dec(v_fuel_849_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_860_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_858_; 
v___x_854_ = lean_unsigned_to_nat(0u);
v___x_855_ = lean_nat_dec_eq(v_n_850_, v___x_854_);
lean_dec(v_n_850_);
v___x_856_ = lean_box(v___x_855_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 0, v___x_856_);
v___x_858_ = v___x_852_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_859_; 
v_reuseFailAlloc_859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_859_, 0, v___x_856_);
v___x_858_ = v_reuseFailAlloc_859_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
return v___x_858_;
}
}
}
else
{
uint8_t v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; 
lean_dec(v_fuel_849_);
v___x_861_ = 0;
v___x_862_ = lean_box(v___x_861_);
v___x_863_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_863_, 0, v___x_862_);
return v___x_863_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg___boxed(lean_object* v_a_864_, lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_864_);
lean_dec(v_a_864_);
return v_res_866_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(lean_object* v_a_867_, lean_object* v_a_868_, lean_object* v_a_869_, lean_object* v_a_870_, lean_object* v_a_871_, lean_object* v_a_872_, lean_object* v_a_873_, lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_){
_start:
{
lean_object* v___x_879_; 
v___x_879_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_868_);
return v___x_879_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___boxed(lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_, lean_object* v_a_885_, lean_object* v_a_886_, lean_object* v_a_887_, lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_){
_start:
{
lean_object* v_res_892_; 
v_res_892_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_, v_a_885_, v_a_886_, v_a_887_, v_a_888_, v_a_889_, v_a_890_);
lean_dec(v_a_890_);
lean_dec_ref(v_a_889_);
lean_dec(v_a_888_);
lean_dec_ref(v_a_887_);
lean_dec(v_a_886_);
lean_dec_ref(v_a_885_);
lean_dec(v_a_884_);
lean_dec_ref(v_a_883_);
lean_dec(v_a_882_);
lean_dec(v_a_881_);
lean_dec_ref(v_a_880_);
return v_res_892_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object* v_a_893_){
_start:
{
lean_object* v___x_895_; lean_object* v_specBackwardRuleCache_896_; lean_object* v_splitBackwardRuleCache_897_; lean_object* v_latticeBackwardRuleCache_898_; lean_object* v_frameBackwardRuleCache_899_; lean_object* v_frameDB_900_; lean_object* v_invariants_901_; lean_object* v_vcs_902_; lean_object* v_simpState_903_; lean_object* v_fuel_904_; lean_object* v_inlineHandledInvariants_905_; lean_object* v___x_907_; uint8_t v_isShared_908_; uint8_t v_isSharedCheck_930_; 
v___x_895_ = lean_st_ref_take(v_a_893_);
v_specBackwardRuleCache_896_ = lean_ctor_get(v___x_895_, 0);
v_splitBackwardRuleCache_897_ = lean_ctor_get(v___x_895_, 1);
v_latticeBackwardRuleCache_898_ = lean_ctor_get(v___x_895_, 2);
v_frameBackwardRuleCache_899_ = lean_ctor_get(v___x_895_, 3);
v_frameDB_900_ = lean_ctor_get(v___x_895_, 4);
v_invariants_901_ = lean_ctor_get(v___x_895_, 5);
v_vcs_902_ = lean_ctor_get(v___x_895_, 6);
v_simpState_903_ = lean_ctor_get(v___x_895_, 7);
v_fuel_904_ = lean_ctor_get(v___x_895_, 8);
v_inlineHandledInvariants_905_ = lean_ctor_get(v___x_895_, 9);
v_isSharedCheck_930_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_930_ == 0)
{
v___x_907_ = v___x_895_;
v_isShared_908_ = v_isSharedCheck_930_;
goto v_resetjp_906_;
}
else
{
lean_inc(v_inlineHandledInvariants_905_);
lean_inc(v_fuel_904_);
lean_inc(v_simpState_903_);
lean_inc(v_vcs_902_);
lean_inc(v_invariants_901_);
lean_inc(v_frameDB_900_);
lean_inc(v_frameBackwardRuleCache_899_);
lean_inc(v_latticeBackwardRuleCache_898_);
lean_inc(v_splitBackwardRuleCache_897_);
lean_inc(v_specBackwardRuleCache_896_);
lean_dec(v___x_895_);
v___x_907_ = lean_box(0);
v_isShared_908_ = v_isSharedCheck_930_;
goto v_resetjp_906_;
}
v_resetjp_906_:
{
lean_object* v___x_909_; lean_object* v___y_911_; 
v___x_909_ = lean_box(0);
if (lean_obj_tag(v_fuel_904_) == 0)
{
lean_object* v_n_917_; lean_object* v_zero_918_; uint8_t v_isZero_919_; 
v_n_917_ = lean_ctor_get(v_fuel_904_, 0);
v_zero_918_ = lean_unsigned_to_nat(0u);
v_isZero_919_ = lean_nat_dec_eq(v_n_917_, v_zero_918_);
if (v_isZero_919_ == 0)
{
lean_object* v___x_921_; uint8_t v_isShared_922_; uint8_t v_isSharedCheck_928_; 
lean_inc(v_n_917_);
v_isSharedCheck_928_ = !lean_is_exclusive(v_fuel_904_);
if (v_isSharedCheck_928_ == 0)
{
lean_object* v_unused_929_; 
v_unused_929_ = lean_ctor_get(v_fuel_904_, 0);
lean_dec(v_unused_929_);
v___x_921_ = v_fuel_904_;
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
else
{
lean_dec(v_fuel_904_);
v___x_921_ = lean_box(0);
v_isShared_922_ = v_isSharedCheck_928_;
goto v_resetjp_920_;
}
v_resetjp_920_:
{
lean_object* v_one_923_; lean_object* v_n_924_; lean_object* v___x_926_; 
v_one_923_ = lean_unsigned_to_nat(1u);
v_n_924_ = lean_nat_sub(v_n_917_, v_one_923_);
lean_dec(v_n_917_);
if (v_isShared_922_ == 0)
{
lean_ctor_set(v___x_921_, 0, v_n_924_);
v___x_926_ = v___x_921_;
goto v_reusejp_925_;
}
else
{
lean_object* v_reuseFailAlloc_927_; 
v_reuseFailAlloc_927_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_927_, 0, v_n_924_);
v___x_926_ = v_reuseFailAlloc_927_;
goto v_reusejp_925_;
}
v_reusejp_925_:
{
v___y_911_ = v___x_926_;
goto v___jp_910_;
}
}
}
else
{
v___y_911_ = v_fuel_904_;
goto v___jp_910_;
}
}
else
{
v___y_911_ = v_fuel_904_;
goto v___jp_910_;
}
v___jp_910_:
{
lean_object* v___x_913_; 
if (v_isShared_908_ == 0)
{
lean_ctor_set(v___x_907_, 8, v___y_911_);
v___x_913_ = v___x_907_;
goto v_reusejp_912_;
}
else
{
lean_object* v_reuseFailAlloc_916_; 
v_reuseFailAlloc_916_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_916_, 0, v_specBackwardRuleCache_896_);
lean_ctor_set(v_reuseFailAlloc_916_, 1, v_splitBackwardRuleCache_897_);
lean_ctor_set(v_reuseFailAlloc_916_, 2, v_latticeBackwardRuleCache_898_);
lean_ctor_set(v_reuseFailAlloc_916_, 3, v_frameBackwardRuleCache_899_);
lean_ctor_set(v_reuseFailAlloc_916_, 4, v_frameDB_900_);
lean_ctor_set(v_reuseFailAlloc_916_, 5, v_invariants_901_);
lean_ctor_set(v_reuseFailAlloc_916_, 6, v_vcs_902_);
lean_ctor_set(v_reuseFailAlloc_916_, 7, v_simpState_903_);
lean_ctor_set(v_reuseFailAlloc_916_, 8, v___y_911_);
lean_ctor_set(v_reuseFailAlloc_916_, 9, v_inlineHandledInvariants_905_);
v___x_913_ = v_reuseFailAlloc_916_;
goto v_reusejp_912_;
}
v_reusejp_912_:
{
lean_object* v___x_914_; lean_object* v___x_915_; 
v___x_914_ = lean_st_ref_set(v_a_893_, v___x_913_);
v___x_915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_915_, 0, v___x_909_);
return v___x_915_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg___boxed(lean_object* v_a_931_, lean_object* v_a_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_931_);
lean_dec(v_a_931_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(lean_object* v_a_934_, lean_object* v_a_935_, lean_object* v_a_936_, lean_object* v_a_937_, lean_object* v_a_938_, lean_object* v_a_939_, lean_object* v_a_940_, lean_object* v_a_941_, lean_object* v_a_942_, lean_object* v_a_943_, lean_object* v_a_944_){
_start:
{
lean_object* v___x_946_; 
v___x_946_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_935_);
return v___x_946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___boxed(lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_, lean_object* v_a_954_, lean_object* v_a_955_, lean_object* v_a_956_, lean_object* v_a_957_, lean_object* v_a_958_){
_start:
{
lean_object* v_res_959_; 
v_res_959_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_, v_a_954_, v_a_955_, v_a_956_, v_a_957_);
lean_dec(v_a_957_);
lean_dec_ref(v_a_956_);
lean_dec(v_a_955_);
lean_dec_ref(v_a_954_);
lean_dec(v_a_953_);
lean_dec_ref(v_a_952_);
lean_dec(v_a_951_);
lean_dec_ref(v_a_950_);
lean_dec(v_a_949_);
lean_dec(v_a_948_);
lean_dec_ref(v_a_947_);
return v_res_959_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
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
l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default = _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default);
l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry = _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry);
l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB = _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameDB);
l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default = _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default);
l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope = _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope();
lean_mark_persistent(l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(uint8_t builtin);
lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Apply(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_DiscrTree(uint8_t builtin);
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Do_VCGen_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_Do_Internal_VCGen_FrameProc(builtin);
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
res = runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_Tactic_Do_Internal_VCGen_Context(builtin);
}
#ifdef __cplusplus
}
#endif
