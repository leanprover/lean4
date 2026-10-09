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
lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules(lean_object* v_a_88_, lean_object* v_a_89_, lean_object* v_a_90_, lean_object* v_a_91_){
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
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_mkBackwardRules_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_88_ = stack[0].m_obj;
lean_object* v_a_89_ = stack[1].m_obj;
lean_object* v_a_90_ = stack[2].m_obj;
lean_object* v_a_91_ = stack[3].m_obj;
lean_object* v_res_234_;
v_res_234_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRules(v_a_88_, v_a_89_, v_a_90_, v_a_91_);
stack->m_obj
 = v_res_234_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_mkBackwardRules___boxed(lean_object* v_a_235_, lean_object* v_a_236_, lean_object* v_a_237_, lean_object* v_a_238_, lean_object* v_a_239_){
_start:
{
lean_object* v_res_240_; 
v_res_240_ = l_Lean_Elab_Tactic_VCGen_mkBackwardRules(v_a_235_, v_a_236_, v_a_237_, v_a_238_);
lean_dec(v_a_238_);
lean_dec_ref(v_a_237_);
lean_dec(v_a_236_);
lean_dec_ref(v_a_235_);
return v_res_240_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0(void){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_241_ = lean_unsigned_to_nat(0u);
v___x_242_ = lean_box(0);
v___x_243_ = lean_box(1);
v___x_244_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_instInhabitedSpecTheorems_default;
v___x_245_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___x_243_);
lean_ctor_set(v___x_245_, 2, v___x_242_);
lean_ctor_set(v___x_245_, 3, v___x_241_);
return v___x_245_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default(void){
_start:
{
lean_object* v___x_246_; 
v___x_246_ = lean_obj_once(&l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0, &l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0_once, _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default___closed__0);
return v___x_246_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_VCGen_instInhabitedScope(void){
_start:
{
lean_object* v___x_247_; 
v___x_247_ = l_Lean_Elab_Tactic_VCGen_instInhabitedScope_default;
return v___x_247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_registerJP(lean_object* v_s_248_, lean_object* v_fv_249_, lean_object* v_info_250_){
_start:
{
lean_object* v_specs_251_; lean_object* v_jps_252_; lean_object* v_lastLiftedPre_x3f_253_; lean_object* v_nextDeclIdx_254_; lean_object* v___x_256_; uint8_t v_isShared_257_; uint8_t v_isSharedCheck_262_; 
v_specs_251_ = lean_ctor_get(v_s_248_, 0);
v_jps_252_ = lean_ctor_get(v_s_248_, 1);
v_lastLiftedPre_x3f_253_ = lean_ctor_get(v_s_248_, 2);
v_nextDeclIdx_254_ = lean_ctor_get(v_s_248_, 3);
v_isSharedCheck_262_ = !lean_is_exclusive(v_s_248_);
if (v_isSharedCheck_262_ == 0)
{
v___x_256_ = v_s_248_;
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
else
{
lean_inc(v_nextDeclIdx_254_);
lean_inc(v_lastLiftedPre_x3f_253_);
lean_inc(v_jps_252_);
lean_inc(v_specs_251_);
lean_dec(v_s_248_);
v___x_256_ = lean_box(0);
v_isShared_257_ = v_isSharedCheck_262_;
goto v_resetjp_255_;
}
v_resetjp_255_:
{
lean_object* v___x_258_; lean_object* v___x_260_; 
v___x_258_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_249_, v_info_250_, v_jps_252_);
if (v_isShared_257_ == 0)
{
lean_ctor_set(v___x_256_, 1, v___x_258_);
v___x_260_ = v___x_256_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v_specs_251_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_261_, 2, v_lastLiftedPre_x3f_253_);
lean_ctor_set(v_reuseFailAlloc_261_, 3, v_nextDeclIdx_254_);
v___x_260_ = v_reuseFailAlloc_261_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
return v___x_260_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(lean_object* v_t_263_, lean_object* v_k_264_){
_start:
{
if (lean_obj_tag(v_t_263_) == 0)
{
lean_object* v_k_265_; lean_object* v_v_266_; lean_object* v_l_267_; lean_object* v_r_268_; uint8_t v___x_269_; 
v_k_265_ = lean_ctor_get(v_t_263_, 1);
v_v_266_ = lean_ctor_get(v_t_263_, 2);
v_l_267_ = lean_ctor_get(v_t_263_, 3);
v_r_268_ = lean_ctor_get(v_t_263_, 4);
v___x_269_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_264_, v_k_265_);
switch(v___x_269_)
{
case 0:
{
v_t_263_ = v_l_267_;
goto _start;
}
case 1:
{
lean_object* v___x_271_; 
lean_inc(v_v_266_);
v___x_271_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_271_, 0, v_v_266_);
return v___x_271_;
}
default: 
{
v_t_263_ = v_r_268_;
goto _start;
}
}
}
else
{
lean_object* v___x_273_; 
v___x_273_ = lean_box(0);
return v___x_273_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_274_, lean_object* v_k_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_274_, v_k_275_);
lean_dec(v_k_275_);
lean_dec(v_t_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f(lean_object* v_s_277_, lean_object* v_fv_278_){
_start:
{
lean_object* v_jps_279_; lean_object* v___x_280_; 
v_jps_279_ = lean_ctor_get(v_s_277_, 1);
v___x_280_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_jps_279_, v_fv_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f___boxed(lean_object* v_s_281_, lean_object* v_fv_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f(v_s_281_, v_fv_282_);
lean_dec(v_fv_282_);
lean_dec_ref(v_s_281_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0(lean_object* v_00_u03b4_284_, lean_object* v_t_285_, lean_object* v_k_286_){
_start:
{
lean_object* v___x_287_; 
v___x_287_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_285_, v_k_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_288_, lean_object* v_t_289_, lean_object* v_k_290_){
_start:
{
lean_object* v_res_291_; 
v_res_291_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_VCGen_Scope_knownJP_x3f_spec__0(v_00_u03b4_288_, v_t_289_, v_k_290_);
lean_dec(v_k_290_);
lean_dec(v_t_289_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(lean_object* v_s_292_, lean_object* v_thm_293_){
_start:
{
lean_object* v_specs_294_; lean_object* v_jps_295_; lean_object* v_lastLiftedPre_x3f_296_; lean_object* v_nextDeclIdx_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_305_; 
v_specs_294_ = lean_ctor_get(v_s_292_, 0);
v_jps_295_ = lean_ctor_get(v_s_292_, 1);
v_lastLiftedPre_x3f_296_ = lean_ctor_get(v_s_292_, 2);
v_nextDeclIdx_297_ = lean_ctor_get(v_s_292_, 3);
v_isSharedCheck_305_ = !lean_is_exclusive(v_s_292_);
if (v_isSharedCheck_305_ == 0)
{
v___x_299_ = v_s_292_;
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_nextDeclIdx_297_);
lean_inc(v_lastLiftedPre_x3f_296_);
lean_inc(v_jps_295_);
lean_inc(v_specs_294_);
lean_dec(v_s_292_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_305_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_SpecTheorems_insert(v_specs_294_, v_thm_293_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_304_; 
v_reuseFailAlloc_304_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_304_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_304_, 1, v_jps_295_);
lean_ctor_set(v_reuseFailAlloc_304_, 2, v_lastLiftedPre_x3f_296_);
lean_ctor_set(v_reuseFailAlloc_304_, 3, v_nextDeclIdx_297_);
v___x_303_ = v_reuseFailAlloc_304_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
return v___x_303_;
}
}
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object* v_x_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_, lean_object* v___y_314_, lean_object* v___y_315_, lean_object* v___y_316_, lean_object* v___y_317_){
_start:
{
lean_object* v___x_319_; 
lean_inc(v___y_313_);
lean_inc_ref(v___y_312_);
lean_inc(v___y_311_);
lean_inc_ref(v___y_310_);
lean_inc(v___y_309_);
lean_inc(v___y_308_);
lean_inc_ref(v___y_307_);
v___x_319_ = lean_apply_12(v_x_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_, lean_box(0));
return v___x_319_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_306_ = stack[0].m_obj;
lean_object* v___y_307_ = stack[1].m_obj;
lean_object* v___y_308_ = stack[2].m_obj;
lean_object* v___y_309_ = stack[3].m_obj;
lean_object* v___y_310_ = stack[4].m_obj;
lean_object* v___y_311_ = stack[5].m_obj;
lean_object* v___y_312_ = stack[6].m_obj;
lean_object* v___y_313_ = stack[7].m_obj;
lean_object* v___y_314_ = stack[8].m_obj;
lean_object* v___y_315_ = stack[9].m_obj;
lean_object* v___y_316_ = stack[10].m_obj;
lean_object* v___y_317_ = stack[11].m_obj;
lean_object* v_res_320_;
v_res_320_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_306_, v___y_307_, v___y_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_, v___y_313_, v___y_314_, v___y_315_, v___y_316_, v___y_317_);
stack->m_obj
 = v_res_320_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object* v_x_321_, lean_object* v___y_322_, lean_object* v___y_323_, lean_object* v___y_324_, lean_object* v___y_325_, lean_object* v___y_326_, lean_object* v___y_327_, lean_object* v___y_328_, lean_object* v___y_329_, lean_object* v___y_330_, lean_object* v___y_331_, lean_object* v___y_332_, lean_object* v___y_333_){
_start:
{
lean_object* v_res_334_; 
v_res_334_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_321_, v___y_322_, v___y_323_, v___y_324_, v___y_325_, v___y_326_, v___y_327_, v___y_328_, v___y_329_, v___y_330_, v___y_331_, v___y_332_);
lean_dec(v___y_328_);
lean_dec_ref(v___y_327_);
lean_dec(v___y_326_);
lean_dec_ref(v___y_325_);
lean_dec(v___y_324_);
lean_dec(v___y_323_);
lean_dec_ref(v___y_322_);
return v_res_334_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object* v_mvarId_335_, lean_object* v_x_336_, lean_object* v___y_337_, lean_object* v___y_338_, lean_object* v___y_339_, lean_object* v___y_340_, lean_object* v___y_341_, lean_object* v___y_342_, lean_object* v___y_343_, lean_object* v___y_344_, lean_object* v___y_345_, lean_object* v___y_346_, lean_object* v___y_347_){
_start:
{
lean_object* v___f_349_; lean_object* v___x_350_; 
lean_inc(v___y_343_);
lean_inc_ref(v___y_342_);
lean_inc(v___y_341_);
lean_inc_ref(v___y_340_);
lean_inc(v___y_339_);
lean_inc(v___y_338_);
lean_inc_ref(v___y_337_);
v___f_349_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_349_, 0, v_x_336_);
lean_closure_set(v___f_349_, 1, v___y_337_);
lean_closure_set(v___f_349_, 2, v___y_338_);
lean_closure_set(v___f_349_, 3, v___y_339_);
lean_closure_set(v___f_349_, 4, v___y_340_);
lean_closure_set(v___f_349_, 5, v___y_341_);
lean_closure_set(v___f_349_, 6, v___y_342_);
lean_closure_set(v___f_349_, 7, v___y_343_);
v___x_350_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_335_, v___f_349_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
if (lean_obj_tag(v___x_350_) == 0)
{
return v___x_350_;
}
else
{
lean_object* v_a_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_358_; 
v_a_351_ = lean_ctor_get(v___x_350_, 0);
v_isSharedCheck_358_ = !lean_is_exclusive(v___x_350_);
if (v_isSharedCheck_358_ == 0)
{
v___x_353_ = v___x_350_;
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_a_351_);
lean_dec(v___x_350_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_358_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_356_; 
if (v_isShared_354_ == 0)
{
v___x_356_ = v___x_353_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_a_351_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
return v___x_356_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_335_ = stack[0].m_obj;
lean_object* v_x_336_ = stack[1].m_obj;
lean_object* v___y_337_ = stack[2].m_obj;
lean_object* v___y_338_ = stack[3].m_obj;
lean_object* v___y_339_ = stack[4].m_obj;
lean_object* v___y_340_ = stack[5].m_obj;
lean_object* v___y_341_ = stack[6].m_obj;
lean_object* v___y_342_ = stack[7].m_obj;
lean_object* v___y_343_ = stack[8].m_obj;
lean_object* v___y_344_ = stack[9].m_obj;
lean_object* v___y_345_ = stack[10].m_obj;
lean_object* v___y_346_ = stack[11].m_obj;
lean_object* v___y_347_ = stack[12].m_obj;
lean_object* v_res_359_;
v_res_359_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_335_, v_x_336_, v___y_337_, v___y_338_, v___y_339_, v___y_340_, v___y_341_, v___y_342_, v___y_343_, v___y_344_, v___y_345_, v___y_346_, v___y_347_);
stack->m_obj
 = v_res_359_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object* v_mvarId_360_, lean_object* v_x_361_, lean_object* v___y_362_, lean_object* v___y_363_, lean_object* v___y_364_, lean_object* v___y_365_, lean_object* v___y_366_, lean_object* v___y_367_, lean_object* v___y_368_, lean_object* v___y_369_, lean_object* v___y_370_, lean_object* v___y_371_, lean_object* v___y_372_, lean_object* v___y_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_360_, v_x_361_, v___y_362_, v___y_363_, v___y_364_, v___y_365_, v___y_366_, v___y_367_, v___y_368_, v___y_369_, v___y_370_, v___y_371_, v___y_372_);
lean_dec(v___y_372_);
lean_dec_ref(v___y_371_);
lean_dec(v___y_370_);
lean_dec_ref(v___y_369_);
lean_dec(v___y_368_);
lean_dec_ref(v___y_367_);
lean_dec(v___y_366_);
lean_dec_ref(v___y_365_);
lean_dec(v___y_364_);
lean_dec(v___y_363_);
lean_dec_ref(v___y_362_);
return v_res_374_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(lean_object* v_00_u03b1_375_, lean_object* v_mvarId_376_, lean_object* v_x_377_, lean_object* v___y_378_, lean_object* v___y_379_, lean_object* v___y_380_, lean_object* v___y_381_, lean_object* v___y_382_, lean_object* v___y_383_, lean_object* v___y_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_376_, v_x_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_390_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_376_ = stack[1].m_obj;
lean_object* v_x_377_ = stack[2].m_obj;
lean_object* v___y_378_ = stack[3].m_obj;
lean_object* v___y_379_ = stack[4].m_obj;
lean_object* v___y_380_ = stack[5].m_obj;
lean_object* v___y_381_ = stack[6].m_obj;
lean_object* v___y_382_ = stack[7].m_obj;
lean_object* v___y_383_ = stack[8].m_obj;
lean_object* v___y_384_ = stack[9].m_obj;
lean_object* v___y_385_ = stack[10].m_obj;
lean_object* v___y_386_ = stack[11].m_obj;
lean_object* v___y_387_ = stack[12].m_obj;
lean_object* v___y_388_ = stack[13].m_obj;
lean_object* v_res_391_;
v_res_391_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(lean_box(0), v_mvarId_376_, v_x_377_, v___y_378_, v___y_379_, v___y_380_, v___y_381_, v___y_382_, v___y_383_, v___y_384_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
stack->m_obj
 = v_res_391_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object* v_00_u03b1_392_, lean_object* v_mvarId_393_, lean_object* v_x_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_, lean_object* v___y_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_392_, v_mvarId_393_, v_x_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_, v___y_402_, v___y_403_, v___y_404_, v___y_405_);
lean_dec(v___y_405_);
lean_dec_ref(v___y_404_);
lean_dec(v___y_403_);
lean_dec_ref(v___y_402_);
lean_dec(v___y_401_);
lean_dec_ref(v___y_400_);
lean_dec(v___y_399_);
lean_dec_ref(v___y_398_);
lean_dec(v___y_397_);
lean_dec(v___y_396_);
lean_dec_ref(v___y_395_);
return v_res_407_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object* v_as_408_, size_t v_i_409_, size_t v_stop_410_, lean_object* v_b_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_, lean_object* v___y_415_){
_start:
{
lean_object* v_a_418_; uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_eq(v_i_409_, v_stop_410_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; 
v___x_423_ = lean_array_uget_borrowed(v_as_408_, v_i_409_);
if (lean_obj_tag(v___x_423_) == 0)
{
v_a_418_ = v_b_411_;
goto v___jp_417_;
}
else
{
lean_object* v_val_424_; uint8_t v___x_425_; 
v_val_424_ = lean_ctor_get(v___x_423_, 0);
v___x_425_ = l_Lean_LocalDecl_isAuxDecl(v_val_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_426_ = l_Lean_LocalDecl_fvarId(v_val_424_);
v___x_427_ = lean_unsigned_to_nat(100u);
v___x_428_ = l_Lean_Elab_Tactic_VCGen_SpecAttr_mkSpecTheoremFromLocal(v___x_426_, v___x_427_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
if (lean_obj_tag(v___x_428_) == 0)
{
lean_object* v_a_429_; 
v_a_429_ = lean_ctor_get(v___x_428_, 0);
lean_inc(v_a_429_);
lean_dec_ref_known(v___x_428_, 1);
if (lean_obj_tag(v_a_429_) == 1)
{
lean_object* v_val_430_; lean_object* v___x_431_; 
v_val_430_ = lean_ctor_get(v_a_429_, 0);
lean_inc(v_val_430_);
lean_dec_ref_known(v_a_429_, 1);
v___x_431_ = l_Lean_Elab_Tactic_VCGen_Scope_insertSpec(v_b_411_, v_val_430_);
v_a_418_ = v___x_431_;
goto v___jp_417_;
}
else
{
lean_dec(v_a_429_);
v_a_418_ = v_b_411_;
goto v___jp_417_;
}
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_443_; 
v_a_432_ = lean_ctor_get(v___x_428_, 0);
v_isSharedCheck_443_ = !lean_is_exclusive(v___x_428_);
if (v_isSharedCheck_443_ == 0)
{
v___x_434_ = v___x_428_;
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_428_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_443_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
uint8_t v___y_437_; uint8_t v___x_441_; 
v___x_441_ = l_Lean_Exception_isInterrupt(v_a_432_);
if (v___x_441_ == 0)
{
uint8_t v___x_442_; 
lean_inc(v_a_432_);
v___x_442_ = l_Lean_Exception_isRuntime(v_a_432_);
v___y_437_ = v___x_442_;
goto v___jp_436_;
}
else
{
v___y_437_ = v___x_441_;
goto v___jp_436_;
}
v___jp_436_:
{
if (v___y_437_ == 0)
{
lean_del_object(v___x_434_);
lean_dec(v_a_432_);
v_a_418_ = v_b_411_;
goto v___jp_417_;
}
else
{
lean_object* v___x_439_; 
lean_dec_ref(v_b_411_);
if (v_isShared_435_ == 0)
{
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_440_; 
v_reuseFailAlloc_440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_440_, 0, v_a_432_);
v___x_439_ = v_reuseFailAlloc_440_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
return v___x_439_;
}
}
}
}
}
}
else
{
v_a_418_ = v_b_411_;
goto v___jp_417_;
}
}
}
else
{
lean_object* v___x_444_; 
v___x_444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_444_, 0, v_b_411_);
return v___x_444_;
}
v___jp_417_:
{
size_t v___x_419_; size_t v___x_420_; 
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_409_, v___x_419_);
v_i_409_ = v___x_420_;
v_b_411_ = v_a_418_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_408_ = stack[0].m_obj;
size_t v_i_409_ = stack[1].m_num;
size_t v_stop_410_ = stack[2].m_num;
lean_object* v_b_411_ = stack[3].m_obj;
lean_object* v___y_412_ = stack[4].m_obj;
lean_object* v___y_413_ = stack[5].m_obj;
lean_object* v___y_414_ = stack[6].m_obj;
lean_object* v___y_415_ = stack[7].m_obj;
lean_object* v_res_445_;
v_res_445_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_408_, v_i_409_, v_stop_410_, v_b_411_, v___y_412_, v___y_413_, v___y_414_, v___y_415_);
stack->m_obj
 = v_res_445_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_as_446_, lean_object* v_i_447_, lean_object* v_stop_448_, lean_object* v_b_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
size_t v_i_boxed_455_; size_t v_stop_boxed_456_; lean_object* v_res_457_; 
v_i_boxed_455_ = lean_unbox_usize(v_i_447_);
lean_dec(v_i_447_);
v_stop_boxed_456_ = lean_unbox_usize(v_stop_448_);
lean_dec(v_stop_448_);
v_res_457_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_446_, v_i_boxed_455_, v_stop_boxed_456_, v_b_449_, v___y_450_, v___y_451_, v___y_452_, v___y_453_);
lean_dec(v___y_453_);
lean_dec_ref(v___y_452_);
lean_dec(v___y_451_);
lean_dec_ref(v___y_450_);
lean_dec_ref(v_as_446_);
return v_res_457_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object* v_x_458_, lean_object* v_x_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_, lean_object* v___y_469_, lean_object* v___y_470_){
_start:
{
if (lean_obj_tag(v_x_458_) == 0)
{
lean_object* v_cs_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_485_; 
v_cs_472_ = lean_ctor_get(v_x_458_, 0);
v_isSharedCheck_485_ = !lean_is_exclusive(v_x_458_);
if (v_isSharedCheck_485_ == 0)
{
v___x_474_ = v_x_458_;
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_cs_472_);
lean_dec(v_x_458_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_485_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_476_ = lean_unsigned_to_nat(0u);
v___x_477_ = lean_array_get_size(v_cs_472_);
v___x_478_ = lean_nat_dec_lt(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_480_; 
lean_dec_ref(v_cs_472_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 0, v_x_459_);
v___x_480_ = v___x_474_;
goto v_reusejp_479_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v_x_459_);
v___x_480_ = v_reuseFailAlloc_481_;
goto v_reusejp_479_;
}
v_reusejp_479_:
{
return v___x_480_;
}
}
else
{
size_t v___x_482_; size_t v___x_483_; lean_object* v___x_484_; 
lean_del_object(v___x_474_);
v___x_482_ = ((size_t)0ULL);
v___x_483_ = lean_usize_of_nat(v___x_477_);
v___x_484_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_472_, v___x_482_, v___x_483_, v_x_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec_ref(v_cs_472_);
return v___x_484_;
}
}
}
else
{
lean_object* v_vs_486_; lean_object* v___x_488_; uint8_t v_isShared_489_; uint8_t v_isSharedCheck_499_; 
v_vs_486_ = lean_ctor_get(v_x_458_, 0);
v_isSharedCheck_499_ = !lean_is_exclusive(v_x_458_);
if (v_isSharedCheck_499_ == 0)
{
v___x_488_ = v_x_458_;
v_isShared_489_ = v_isSharedCheck_499_;
goto v_resetjp_487_;
}
else
{
lean_inc(v_vs_486_);
lean_dec(v_x_458_);
v___x_488_ = lean_box(0);
v_isShared_489_ = v_isSharedCheck_499_;
goto v_resetjp_487_;
}
v_resetjp_487_:
{
lean_object* v___x_490_; lean_object* v___x_491_; uint8_t v___x_492_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = lean_array_get_size(v_vs_486_);
v___x_492_ = lean_nat_dec_lt(v___x_490_, v___x_491_);
if (v___x_492_ == 0)
{
lean_object* v___x_494_; 
lean_dec_ref(v_vs_486_);
if (v_isShared_489_ == 0)
{
lean_ctor_set_tag(v___x_488_, 0);
lean_ctor_set(v___x_488_, 0, v_x_459_);
v___x_494_ = v___x_488_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v_x_459_);
v___x_494_ = v_reuseFailAlloc_495_;
goto v_reusejp_493_;
}
v_reusejp_493_:
{
return v___x_494_;
}
}
else
{
size_t v___x_496_; size_t v___x_497_; lean_object* v___x_498_; 
lean_del_object(v___x_488_);
v___x_496_ = ((size_t)0ULL);
v___x_497_ = lean_usize_of_nat(v___x_491_);
v___x_498_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_486_, v___x_496_, v___x_497_, v_x_459_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
lean_dec_ref(v_vs_486_);
return v___x_498_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_458_ = stack[0].m_obj;
lean_object* v_x_459_ = stack[1].m_obj;
lean_object* v___y_460_ = stack[2].m_obj;
lean_object* v___y_461_ = stack[3].m_obj;
lean_object* v___y_462_ = stack[4].m_obj;
lean_object* v___y_463_ = stack[5].m_obj;
lean_object* v___y_464_ = stack[6].m_obj;
lean_object* v___y_465_ = stack[7].m_obj;
lean_object* v___y_466_ = stack[8].m_obj;
lean_object* v___y_467_ = stack[9].m_obj;
lean_object* v___y_468_ = stack[10].m_obj;
lean_object* v___y_469_ = stack[11].m_obj;
lean_object* v___y_470_ = stack[12].m_obj;
lean_object* v_res_500_;
v_res_500_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_458_, v_x_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_, v___y_469_, v___y_470_);
stack->m_obj
 = v_res_500_;
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_501_, size_t v_i_502_, size_t v_stop_503_, lean_object* v_b_504_, lean_object* v___y_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_){
_start:
{
uint8_t v___x_517_; 
v___x_517_ = lean_usize_dec_eq(v_i_502_, v_stop_503_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_array_uget_borrowed(v_as_501_, v_i_502_);
lean_inc(v___x_518_);
v___x_519_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_518_, v_b_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
if (lean_obj_tag(v___x_519_) == 0)
{
lean_object* v_a_520_; size_t v___x_521_; size_t v___x_522_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
lean_inc(v_a_520_);
lean_dec_ref_known(v___x_519_, 1);
v___x_521_ = ((size_t)1ULL);
v___x_522_ = lean_usize_add(v_i_502_, v___x_521_);
v_i_502_ = v___x_522_;
v_b_504_ = v_a_520_;
goto _start;
}
else
{
return v___x_519_;
}
}
else
{
lean_object* v___x_524_; 
v___x_524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_524_, 0, v_b_504_);
return v___x_524_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_501_ = stack[0].m_obj;
size_t v_i_502_ = stack[1].m_num;
size_t v_stop_503_ = stack[2].m_num;
lean_object* v_b_504_ = stack[3].m_obj;
lean_object* v___y_505_ = stack[4].m_obj;
lean_object* v___y_506_ = stack[5].m_obj;
lean_object* v___y_507_ = stack[6].m_obj;
lean_object* v___y_508_ = stack[7].m_obj;
lean_object* v___y_509_ = stack[8].m_obj;
lean_object* v___y_510_ = stack[9].m_obj;
lean_object* v___y_511_ = stack[10].m_obj;
lean_object* v___y_512_ = stack[11].m_obj;
lean_object* v___y_513_ = stack[12].m_obj;
lean_object* v___y_514_ = stack[13].m_obj;
lean_object* v___y_515_ = stack[14].m_obj;
lean_object* v_res_525_;
v_res_525_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_501_, v_i_502_, v_stop_503_, v_b_504_, v___y_505_, v___y_506_, v___y_507_, v___y_508_, v___y_509_, v___y_510_, v___y_511_, v___y_512_, v___y_513_, v___y_514_, v___y_515_);
stack->m_obj
 = v_res_525_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_526_, lean_object* v_i_527_, lean_object* v_stop_528_, lean_object* v_b_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
size_t v_i_boxed_542_; size_t v_stop_boxed_543_; lean_object* v_res_544_; 
v_i_boxed_542_ = lean_unbox_usize(v_i_527_);
lean_dec(v_i_527_);
v_stop_boxed_543_ = lean_unbox_usize(v_stop_528_);
lean_dec(v_stop_528_);
v_res_544_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_526_, v_i_boxed_542_, v_stop_boxed_543_, v_b_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
lean_dec(v___y_540_);
lean_dec_ref(v___y_539_);
lean_dec(v___y_538_);
lean_dec_ref(v___y_537_);
lean_dec(v___y_536_);
lean_dec_ref(v___y_535_);
lean_dec(v___y_534_);
lean_dec_ref(v___y_533_);
lean_dec(v___y_532_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec_ref(v_as_526_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object* v_x_545_, lean_object* v_x_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_, lean_object* v___y_557_, lean_object* v___y_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_545_, v_x_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_, v___y_557_);
lean_dec(v___y_557_);
lean_dec_ref(v___y_556_);
lean_dec(v___y_555_);
lean_dec_ref(v___y_554_);
lean_dec(v___y_553_);
lean_dec_ref(v___y_552_);
lean_dec(v___y_551_);
lean_dec_ref(v___y_550_);
lean_dec(v___y_549_);
lean_dec(v___y_548_);
lean_dec_ref(v___y_547_);
return v_res_559_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = l_Lean_instInhabitedPersistentArrayNode_default___redArg();
return v___x_560_;
}
}
lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object* v_x_561_, size_t v_x_562_, size_t v_x_563_, lean_object* v_x_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_, lean_object* v___y_574_, lean_object* v___y_575_){
_start:
{
if (lean_obj_tag(v_x_561_) == 0)
{
lean_object* v_cs_577_; lean_object* v___x_578_; size_t v___x_579_; lean_object* v_j_580_; lean_object* v___x_581_; size_t v___x_582_; size_t v___x_583_; size_t v___x_584_; size_t v___x_585_; size_t v___x_586_; size_t v___x_587_; lean_object* v___x_588_; 
v_cs_577_ = lean_ctor_get(v_x_561_, 0);
lean_inc_ref(v_cs_577_);
lean_dec_ref_known(v_x_561_, 1);
v___x_578_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
v___x_579_ = lean_usize_shift_right(v_x_562_, v_x_563_);
v_j_580_ = lean_usize_to_nat(v___x_579_);
v___x_581_ = lean_array_get_borrowed(v___x_578_, v_cs_577_, v_j_580_);
v___x_582_ = ((size_t)1ULL);
v___x_583_ = lean_usize_shift_left(v___x_582_, v_x_563_);
v___x_584_ = lean_usize_sub(v___x_583_, v___x_582_);
v___x_585_ = lean_usize_land(v_x_562_, v___x_584_);
v___x_586_ = ((size_t)5ULL);
v___x_587_ = lean_usize_sub(v_x_563_, v___x_586_);
lean_inc(v___x_581_);
v___x_588_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_581_, v___x_585_, v___x_587_, v_x_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v_a_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; uint8_t v___x_593_; 
v_a_589_ = lean_ctor_get(v___x_588_, 0);
v___x_590_ = lean_unsigned_to_nat(1u);
v___x_591_ = lean_nat_add(v_j_580_, v___x_590_);
lean_dec(v_j_580_);
v___x_592_ = lean_array_get_size(v_cs_577_);
v___x_593_ = lean_nat_dec_lt(v___x_591_, v___x_592_);
if (v___x_593_ == 0)
{
lean_dec(v___x_591_);
lean_dec_ref(v_cs_577_);
return v___x_588_;
}
else
{
size_t v___x_594_; size_t v___x_595_; lean_object* v___x_596_; 
lean_inc(v_a_589_);
lean_dec_ref_known(v___x_588_, 1);
v___x_594_ = lean_usize_of_nat(v___x_591_);
lean_dec(v___x_591_);
v___x_595_ = lean_usize_of_nat(v___x_592_);
v___x_596_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_577_, v___x_594_, v___x_595_, v_a_589_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec_ref(v_cs_577_);
return v___x_596_;
}
}
else
{
lean_dec(v_j_580_);
lean_dec_ref(v_cs_577_);
return v___x_588_;
}
}
else
{
lean_object* v_vs_597_; lean_object* v___x_599_; uint8_t v_isShared_600_; uint8_t v_isSharedCheck_610_; 
v_vs_597_ = lean_ctor_get(v_x_561_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_561_);
if (v_isSharedCheck_610_ == 0)
{
v___x_599_ = v_x_561_;
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
else
{
lean_inc(v_vs_597_);
lean_dec(v_x_561_);
v___x_599_ = lean_box(0);
v_isShared_600_ = v_isSharedCheck_610_;
goto v_resetjp_598_;
}
v_resetjp_598_:
{
lean_object* v___x_601_; lean_object* v___x_602_; uint8_t v___x_603_; 
v___x_601_ = lean_usize_to_nat(v_x_562_);
v___x_602_ = lean_array_get_size(v_vs_597_);
v___x_603_ = lean_nat_dec_lt(v___x_601_, v___x_602_);
if (v___x_603_ == 0)
{
lean_object* v___x_605_; 
lean_dec(v___x_601_);
lean_dec_ref(v_vs_597_);
if (v_isShared_600_ == 0)
{
lean_ctor_set_tag(v___x_599_, 0);
lean_ctor_set(v___x_599_, 0, v_x_564_);
v___x_605_ = v___x_599_;
goto v_reusejp_604_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_x_564_);
v___x_605_ = v_reuseFailAlloc_606_;
goto v_reusejp_604_;
}
v_reusejp_604_:
{
return v___x_605_;
}
}
else
{
size_t v___x_607_; size_t v___x_608_; lean_object* v___x_609_; 
lean_del_object(v___x_599_);
v___x_607_ = lean_usize_of_nat(v___x_601_);
lean_dec(v___x_601_);
v___x_608_ = lean_usize_of_nat(v___x_602_);
v___x_609_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_597_, v___x_607_, v___x_608_, v_x_564_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
lean_dec_ref(v_vs_597_);
return v___x_609_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_561_ = stack[0].m_obj;
size_t v_x_562_ = stack[1].m_num;
size_t v_x_563_ = stack[2].m_num;
lean_object* v_x_564_ = stack[3].m_obj;
lean_object* v___y_565_ = stack[4].m_obj;
lean_object* v___y_566_ = stack[5].m_obj;
lean_object* v___y_567_ = stack[6].m_obj;
lean_object* v___y_568_ = stack[7].m_obj;
lean_object* v___y_569_ = stack[8].m_obj;
lean_object* v___y_570_ = stack[9].m_obj;
lean_object* v___y_571_ = stack[10].m_obj;
lean_object* v___y_572_ = stack[11].m_obj;
lean_object* v___y_573_ = stack[12].m_obj;
lean_object* v___y_574_ = stack[13].m_obj;
lean_object* v___y_575_ = stack[14].m_obj;
lean_object* v_res_611_;
v_res_611_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_561_, v_x_562_, v_x_563_, v_x_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_, v___y_573_, v___y_574_, v___y_575_);
stack->m_obj
 = v_res_611_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_612_, lean_object* v_x_613_, lean_object* v_x_614_, lean_object* v_x_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_){
_start:
{
size_t v_x_19364__boxed_628_; size_t v_x_19365__boxed_629_; lean_object* v_res_630_; 
v_x_19364__boxed_628_ = lean_unbox_usize(v_x_613_);
lean_dec(v_x_613_);
v_x_19365__boxed_629_ = lean_unbox_usize(v_x_614_);
lean_dec(v_x_614_);
v_res_630_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_612_, v_x_19364__boxed_628_, v_x_19365__boxed_629_, v_x_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec_ref(v___y_621_);
lean_dec(v___y_620_);
lean_dec_ref(v___y_619_);
lean_dec(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
return v_res_630_;
}
}
lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object* v_t_631_, lean_object* v_init_632_, lean_object* v_start_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_){
_start:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = lean_unsigned_to_nat(0u);
v___x_647_ = lean_nat_dec_eq(v_start_633_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v_root_648_; lean_object* v_tail_649_; size_t v_shift_650_; lean_object* v_tailOff_651_; uint8_t v___x_652_; 
v_root_648_ = lean_ctor_get(v_t_631_, 0);
lean_inc_ref(v_root_648_);
v_tail_649_ = lean_ctor_get(v_t_631_, 1);
lean_inc_ref(v_tail_649_);
v_shift_650_ = lean_ctor_get_usize(v_t_631_, 4);
v_tailOff_651_ = lean_ctor_get(v_t_631_, 3);
lean_inc(v_tailOff_651_);
lean_dec_ref(v_t_631_);
v___x_652_ = lean_nat_dec_le(v_tailOff_651_, v_start_633_);
if (v___x_652_ == 0)
{
size_t v___x_653_; lean_object* v___x_654_; 
lean_dec(v_tailOff_651_);
v___x_653_ = lean_usize_of_nat(v_start_633_);
v___x_654_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_648_, v___x_653_, v_shift_650_, v_init_632_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_654_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; uint8_t v___x_657_; 
v_a_655_ = lean_ctor_get(v___x_654_, 0);
v___x_656_ = lean_array_get_size(v_tail_649_);
v___x_657_ = lean_nat_dec_lt(v___x_646_, v___x_656_);
if (v___x_657_ == 0)
{
lean_dec_ref(v_tail_649_);
return v___x_654_;
}
else
{
size_t v___x_658_; size_t v___x_659_; lean_object* v___x_660_; 
lean_inc(v_a_655_);
lean_dec_ref_known(v___x_654_, 1);
v___x_658_ = ((size_t)0ULL);
v___x_659_ = lean_usize_of_nat(v___x_656_);
v___x_660_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_649_, v___x_658_, v___x_659_, v_a_655_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec_ref(v_tail_649_);
return v___x_660_;
}
}
else
{
lean_dec_ref(v_tail_649_);
return v___x_654_;
}
}
else
{
lean_object* v___x_661_; lean_object* v___x_662_; uint8_t v___x_663_; 
lean_dec_ref(v_root_648_);
v___x_661_ = lean_nat_sub(v_start_633_, v_tailOff_651_);
lean_dec(v_tailOff_651_);
v___x_662_ = lean_array_get_size(v_tail_649_);
v___x_663_ = lean_nat_dec_lt(v___x_661_, v___x_662_);
if (v___x_663_ == 0)
{
lean_object* v___x_664_; 
lean_dec(v___x_661_);
lean_dec_ref(v_tail_649_);
v___x_664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_664_, 0, v_init_632_);
return v___x_664_;
}
else
{
size_t v___x_665_; size_t v___x_666_; lean_object* v___x_667_; 
v___x_665_ = lean_usize_of_nat(v___x_661_);
lean_dec(v___x_661_);
v___x_666_ = lean_usize_of_nat(v___x_662_);
v___x_667_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_649_, v___x_665_, v___x_666_, v_init_632_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec_ref(v_tail_649_);
return v___x_667_;
}
}
}
else
{
lean_object* v_root_668_; lean_object* v_tail_669_; lean_object* v___x_670_; 
v_root_668_ = lean_ctor_get(v_t_631_, 0);
lean_inc_ref(v_root_668_);
v_tail_669_ = lean_ctor_get(v_t_631_, 1);
lean_inc_ref(v_tail_669_);
lean_dec_ref(v_t_631_);
v___x_670_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_668_, v_init_632_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
if (lean_obj_tag(v___x_670_) == 0)
{
lean_object* v_a_671_; lean_object* v___x_672_; uint8_t v___x_673_; 
v_a_671_ = lean_ctor_get(v___x_670_, 0);
v___x_672_ = lean_array_get_size(v_tail_669_);
v___x_673_ = lean_nat_dec_lt(v___x_646_, v___x_672_);
if (v___x_673_ == 0)
{
lean_dec_ref(v_tail_669_);
return v___x_670_;
}
else
{
size_t v___x_674_; size_t v___x_675_; lean_object* v___x_676_; 
lean_inc(v_a_671_);
lean_dec_ref_known(v___x_670_, 1);
v___x_674_ = ((size_t)0ULL);
v___x_675_ = lean_usize_of_nat(v___x_672_);
v___x_676_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_669_, v___x_674_, v___x_675_, v_a_671_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
lean_dec_ref(v_tail_669_);
return v___x_676_;
}
}
else
{
lean_dec_ref(v_tail_669_);
return v___x_670_;
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_t_631_ = stack[0].m_obj;
lean_object* v_init_632_ = stack[1].m_obj;
lean_object* v_start_633_ = stack[2].m_obj;
lean_object* v___y_634_ = stack[3].m_obj;
lean_object* v___y_635_ = stack[4].m_obj;
lean_object* v___y_636_ = stack[5].m_obj;
lean_object* v___y_637_ = stack[6].m_obj;
lean_object* v___y_638_ = stack[7].m_obj;
lean_object* v___y_639_ = stack[8].m_obj;
lean_object* v___y_640_ = stack[9].m_obj;
lean_object* v___y_641_ = stack[10].m_obj;
lean_object* v___y_642_ = stack[11].m_obj;
lean_object* v___y_643_ = stack[12].m_obj;
lean_object* v___y_644_ = stack[13].m_obj;
lean_object* v_res_677_;
v_res_677_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_631_, v_init_632_, v_start_633_, v___y_634_, v___y_635_, v___y_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_);
stack->m_obj
 = v_res_677_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object* v_t_678_, lean_object* v_init_679_, lean_object* v_start_680_, lean_object* v___y_681_, lean_object* v___y_682_, lean_object* v___y_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_){
_start:
{
lean_object* v_res_693_; 
v_res_693_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_678_, v_init_679_, v_start_680_, v___y_681_, v___y_682_, v___y_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_);
lean_dec(v___y_691_);
lean_dec_ref(v___y_690_);
lean_dec(v___y_689_);
lean_dec_ref(v___y_688_);
lean_dec(v___y_687_);
lean_dec_ref(v___y_686_);
lean_dec(v___y_685_);
lean_dec_ref(v___y_684_);
lean_dec(v___y_683_);
lean_dec(v___y_682_);
lean_dec_ref(v___y_681_);
lean_dec(v_start_680_);
return v_res_693_;
}
}
lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(lean_object* v_lctx_694_, lean_object* v_init_695_, lean_object* v_start_696_, lean_object* v___y_697_, lean_object* v___y_698_, lean_object* v___y_699_, lean_object* v___y_700_, lean_object* v___y_701_, lean_object* v___y_702_, lean_object* v___y_703_, lean_object* v___y_704_, lean_object* v___y_705_, lean_object* v___y_706_, lean_object* v___y_707_){
_start:
{
lean_object* v_decls_709_; lean_object* v___x_710_; 
v_decls_709_ = lean_ctor_get(v_lctx_694_, 1);
lean_inc_ref(v_decls_709_);
lean_dec_ref(v_lctx_694_);
v___x_710_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_709_, v_init_695_, v_start_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
return v___x_710_;
}
}
LEAN_EXPORT void l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_lctx_694_ = stack[0].m_obj;
lean_object* v_init_695_ = stack[1].m_obj;
lean_object* v_start_696_ = stack[2].m_obj;
lean_object* v___y_697_ = stack[3].m_obj;
lean_object* v___y_698_ = stack[4].m_obj;
lean_object* v___y_699_ = stack[5].m_obj;
lean_object* v___y_700_ = stack[6].m_obj;
lean_object* v___y_701_ = stack[7].m_obj;
lean_object* v___y_702_ = stack[8].m_obj;
lean_object* v___y_703_ = stack[9].m_obj;
lean_object* v___y_704_ = stack[10].m_obj;
lean_object* v___y_705_ = stack[11].m_obj;
lean_object* v___y_706_ = stack[12].m_obj;
lean_object* v___y_707_ = stack[13].m_obj;
lean_object* v_res_711_;
v_res_711_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_694_, v_init_695_, v_start_696_, v___y_697_, v___y_698_, v___y_699_, v___y_700_, v___y_701_, v___y_702_, v___y_703_, v___y_704_, v___y_705_, v___y_706_, v___y_707_);
stack->m_obj
 = v_res_711_;
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object* v_lctx_712_, lean_object* v_init_713_, lean_object* v_start_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_712_, v_init_713_, v_start_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_);
lean_dec(v___y_725_);
lean_dec_ref(v___y_724_);
lean_dec(v___y_723_);
lean_dec_ref(v___y_722_);
lean_dec(v___y_721_);
lean_dec_ref(v___y_720_);
lean_dec(v___y_719_);
lean_dec_ref(v___y_718_);
lean_dec(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v_start_714_);
return v_res_727_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(lean_object* v_scope_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_){
_start:
{
lean_object* v_lctx_741_; lean_object* v_decls_742_; lean_object* v_nextDeclIdx_743_; lean_object* v_size_744_; uint8_t v___x_745_; 
v_lctx_741_ = lean_ctor_get(v___y_736_, 2);
v_decls_742_ = lean_ctor_get(v_lctx_741_, 1);
v_nextDeclIdx_743_ = lean_ctor_get(v_scope_728_, 3);
v_size_744_ = lean_ctor_get(v_decls_742_, 2);
v___x_745_ = lean_nat_dec_eq(v_nextDeclIdx_743_, v_size_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; 
lean_inc(v_nextDeclIdx_743_);
lean_inc_ref(v_lctx_741_);
v___x_746_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_741_, v_scope_728_, v_nextDeclIdx_743_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
lean_dec(v_nextDeclIdx_743_);
if (lean_obj_tag(v___x_746_) == 0)
{
lean_object* v_a_747_; lean_object* v___x_749_; uint8_t v_isShared_750_; uint8_t v_isSharedCheck_765_; 
v_a_747_ = lean_ctor_get(v___x_746_, 0);
v_isSharedCheck_765_ = !lean_is_exclusive(v___x_746_);
if (v_isSharedCheck_765_ == 0)
{
v___x_749_ = v___x_746_;
v_isShared_750_ = v_isSharedCheck_765_;
goto v_resetjp_748_;
}
else
{
lean_inc(v_a_747_);
lean_dec(v___x_746_);
v___x_749_ = lean_box(0);
v_isShared_750_ = v_isSharedCheck_765_;
goto v_resetjp_748_;
}
v_resetjp_748_:
{
lean_object* v_specs_751_; lean_object* v_jps_752_; lean_object* v_lastLiftedPre_x3f_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_763_; 
v_specs_751_ = lean_ctor_get(v_a_747_, 0);
v_jps_752_ = lean_ctor_get(v_a_747_, 1);
v_lastLiftedPre_x3f_753_ = lean_ctor_get(v_a_747_, 2);
v_isSharedCheck_763_ = !lean_is_exclusive(v_a_747_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v_a_747_, 3);
lean_dec(v_unused_764_);
v___x_755_ = v_a_747_;
v_isShared_756_ = v_isSharedCheck_763_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_lastLiftedPre_x3f_753_);
lean_inc(v_jps_752_);
lean_inc(v_specs_751_);
lean_dec(v_a_747_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_763_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_758_; 
lean_inc(v_size_744_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 3, v_size_744_);
v___x_758_ = v___x_755_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v_specs_751_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_jps_752_);
lean_ctor_set(v_reuseFailAlloc_762_, 2, v_lastLiftedPre_x3f_753_);
lean_ctor_set(v_reuseFailAlloc_762_, 3, v_size_744_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_750_ == 0)
{
lean_ctor_set(v___x_749_, 0, v___x_758_);
v___x_760_ = v___x_749_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
else
{
return v___x_746_;
}
}
else
{
lean_object* v___x_766_; 
v___x_766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_766_, 0, v_scope_728_);
return v___x_766_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_scope_728_ = stack[0].m_obj;
lean_object* v___y_729_ = stack[1].m_obj;
lean_object* v___y_730_ = stack[2].m_obj;
lean_object* v___y_731_ = stack[3].m_obj;
lean_object* v___y_732_ = stack[4].m_obj;
lean_object* v___y_733_ = stack[5].m_obj;
lean_object* v___y_734_ = stack[6].m_obj;
lean_object* v___y_735_ = stack[7].m_obj;
lean_object* v___y_736_ = stack[8].m_obj;
lean_object* v___y_737_ = stack[9].m_obj;
lean_object* v___y_738_ = stack[10].m_obj;
lean_object* v___y_739_ = stack[11].m_obj;
lean_object* v_res_767_;
v_res_767_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(v_scope_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_);
stack->m_obj
 = v_res_767_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object* v_scope_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_, lean_object* v___y_772_, lean_object* v___y_773_, lean_object* v___y_774_, lean_object* v___y_775_, lean_object* v___y_776_, lean_object* v___y_777_, lean_object* v___y_778_, lean_object* v___y_779_, lean_object* v___y_780_){
_start:
{
lean_object* v_res_781_; 
v_res_781_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0(v_scope_768_, v___y_769_, v___y_770_, v___y_771_, v___y_772_, v___y_773_, v___y_774_, v___y_775_, v___y_776_, v___y_777_, v___y_778_, v___y_779_);
lean_dec(v___y_779_);
lean_dec_ref(v___y_778_);
lean_dec(v___y_777_);
lean_dec_ref(v___y_776_);
lean_dec(v___y_775_);
lean_dec_ref(v___y_774_);
lean_dec(v___y_773_);
lean_dec_ref(v___y_772_);
lean_dec(v___y_771_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
return v_res_781_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(lean_object* v_scope_782_, lean_object* v_goal_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_, lean_object* v_a_788_, lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_, lean_object* v_a_794_){
_start:
{
lean_object* v___f_796_; lean_object* v___x_797_; 
v___f_796_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_796_, 0, v_scope_782_);
v___x_797_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_783_, v___f_796_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
return v___x_797_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_0interp(lean_interpreter_value* stack)
{
lean_object* v_scope_782_ = stack[0].m_obj;
lean_object* v_goal_783_ = stack[1].m_obj;
lean_object* v_a_784_ = stack[2].m_obj;
lean_object* v_a_785_ = stack[3].m_obj;
lean_object* v_a_786_ = stack[4].m_obj;
lean_object* v_a_787_ = stack[5].m_obj;
lean_object* v_a_788_ = stack[6].m_obj;
lean_object* v_a_789_ = stack[7].m_obj;
lean_object* v_a_790_ = stack[8].m_obj;
lean_object* v_a_791_ = stack[9].m_obj;
lean_object* v_a_792_ = stack[10].m_obj;
lean_object* v_a_793_ = stack[11].m_obj;
lean_object* v_a_794_ = stack[12].m_obj;
lean_object* v_res_798_;
v_res_798_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_782_, v_goal_783_, v_a_784_, v_a_785_, v_a_786_, v_a_787_, v_a_788_, v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_, v_a_794_);
stack->m_obj
 = v_res_798_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs___boxed(lean_object* v_scope_799_, lean_object* v_goal_800_, lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_, lean_object* v_a_807_, lean_object* v_a_808_, lean_object* v_a_809_, lean_object* v_a_810_, lean_object* v_a_811_, lean_object* v_a_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs(v_scope_799_, v_goal_800_, v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_, v_a_807_, v_a_808_, v_a_809_, v_a_810_, v_a_811_);
lean_dec(v_a_811_);
lean_dec_ref(v_a_810_);
lean_dec(v_a_809_);
lean_dec_ref(v_a_808_);
lean_dec(v_a_807_);
lean_dec_ref(v_a_806_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
lean_dec(v_a_802_);
lean_dec_ref(v_a_801_);
return v_res_813_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object* v_as_814_, size_t v_i_815_, size_t v_stop_816_, lean_object* v_b_817_, lean_object* v___y_818_, lean_object* v___y_819_, lean_object* v___y_820_, lean_object* v___y_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_){
_start:
{
lean_object* v___x_830_; 
v___x_830_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_814_, v_i_815_, v_stop_816_, v_b_817_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
return v___x_830_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_814_ = stack[0].m_obj;
size_t v_i_815_ = stack[1].m_num;
size_t v_stop_816_ = stack[2].m_num;
lean_object* v_b_817_ = stack[3].m_obj;
lean_object* v___y_818_ = stack[4].m_obj;
lean_object* v___y_819_ = stack[5].m_obj;
lean_object* v___y_820_ = stack[6].m_obj;
lean_object* v___y_821_ = stack[7].m_obj;
lean_object* v___y_822_ = stack[8].m_obj;
lean_object* v___y_823_ = stack[9].m_obj;
lean_object* v___y_824_ = stack[10].m_obj;
lean_object* v___y_825_ = stack[11].m_obj;
lean_object* v___y_826_ = stack[12].m_obj;
lean_object* v___y_827_ = stack[13].m_obj;
lean_object* v___y_828_ = stack[14].m_obj;
lean_object* v_res_831_;
v_res_831_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_814_, v_i_815_, v_stop_816_, v_b_817_, v___y_818_, v___y_819_, v___y_820_, v___y_821_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_);
stack->m_obj
 = v_res_831_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object* v_as_832_, lean_object* v_i_833_, lean_object* v_stop_834_, lean_object* v_b_835_, lean_object* v___y_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_){
_start:
{
size_t v_i_boxed_848_; size_t v_stop_boxed_849_; lean_object* v_res_850_; 
v_i_boxed_848_ = lean_unbox_usize(v_i_833_);
lean_dec(v_i_833_);
v_stop_boxed_849_ = lean_unbox_usize(v_stop_834_);
lean_dec(v_stop_834_);
v_res_850_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_832_, v_i_boxed_848_, v_stop_boxed_849_, v_b_835_, v___y_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_);
lean_dec(v___y_846_);
lean_dec_ref(v___y_845_);
lean_dec(v___y_844_);
lean_dec_ref(v___y_843_);
lean_dec(v___y_842_);
lean_dec_ref(v___y_841_);
lean_dec(v___y_840_);
lean_dec_ref(v___y_839_);
lean_dec(v___y_838_);
lean_dec(v___y_837_);
lean_dec_ref(v___y_836_);
lean_dec_ref(v_as_832_);
return v_res_850_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(lean_object* v_a_851_){
_start:
{
lean_object* v___x_853_; lean_object* v_fuel_858_; 
v___x_853_ = lean_st_ref_get(v_a_851_);
v_fuel_858_ = lean_ctor_get(v___x_853_, 8);
lean_inc(v_fuel_858_);
lean_dec(v___x_853_);
if (lean_obj_tag(v_fuel_858_) == 0)
{
lean_object* v_n_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_869_; 
v_n_859_ = lean_ctor_get(v_fuel_858_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v_fuel_858_);
if (v_isSharedCheck_869_ == 0)
{
v___x_861_ = v_fuel_858_;
v_isShared_862_ = v_isSharedCheck_869_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_n_859_);
lean_dec(v_fuel_858_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_869_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_863_; uint8_t v___x_864_; 
v___x_863_ = lean_unsigned_to_nat(0u);
v___x_864_ = lean_nat_dec_eq(v_n_859_, v___x_863_);
lean_dec(v_n_859_);
if (v___x_864_ == 0)
{
lean_del_object(v___x_861_);
goto v___jp_854_;
}
else
{
lean_object* v___x_865_; lean_object* v___x_867_; 
v___x_865_ = lean_box(v___x_864_);
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_865_);
v___x_867_ = v___x_861_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v___x_865_);
v___x_867_ = v_reuseFailAlloc_868_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
return v___x_867_;
}
}
}
}
else
{
lean_dec(v_fuel_858_);
goto v___jp_854_;
}
v___jp_854_:
{
uint8_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = 0;
v___x_856_ = lean_box(v___x_855_);
v___x_857_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
return v___x_857_;
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_851_ = stack[0].m_obj;
lean_object* v_res_870_;
v_res_870_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_851_);
stack->m_obj
 = v_res_870_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg___boxed(lean_object* v_a_871_, lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_871_);
lean_dec(v_a_871_);
return v_res_873_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel(lean_object* v_a_874_, lean_object* v_a_875_, lean_object* v_a_876_, lean_object* v_a_877_, lean_object* v_a_878_, lean_object* v_a_879_, lean_object* v_a_880_, lean_object* v_a_881_, lean_object* v_a_882_, lean_object* v_a_883_, lean_object* v_a_884_){
_start:
{
lean_object* v___x_886_; 
v___x_886_ = l_Lean_Elab_Tactic_VCGen_outOfFuel___redArg(v_a_875_);
return v___x_886_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_outOfFuel_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_874_ = stack[0].m_obj;
lean_object* v_a_875_ = stack[1].m_obj;
lean_object* v_a_876_ = stack[2].m_obj;
lean_object* v_a_877_ = stack[3].m_obj;
lean_object* v_a_878_ = stack[4].m_obj;
lean_object* v_a_879_ = stack[5].m_obj;
lean_object* v_a_880_ = stack[6].m_obj;
lean_object* v_a_881_ = stack[7].m_obj;
lean_object* v_a_882_ = stack[8].m_obj;
lean_object* v_a_883_ = stack[9].m_obj;
lean_object* v_a_884_ = stack[10].m_obj;
lean_object* v_res_887_;
v_res_887_ = l_Lean_Elab_Tactic_VCGen_outOfFuel(v_a_874_, v_a_875_, v_a_876_, v_a_877_, v_a_878_, v_a_879_, v_a_880_, v_a_881_, v_a_882_, v_a_883_, v_a_884_);
stack->m_obj
 = v_res_887_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_outOfFuel___boxed(lean_object* v_a_888_, lean_object* v_a_889_, lean_object* v_a_890_, lean_object* v_a_891_, lean_object* v_a_892_, lean_object* v_a_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_){
_start:
{
lean_object* v_res_900_; 
v_res_900_ = l_Lean_Elab_Tactic_VCGen_outOfFuel(v_a_888_, v_a_889_, v_a_890_, v_a_891_, v_a_892_, v_a_893_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_);
lean_dec(v_a_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_a_896_);
lean_dec_ref(v_a_895_);
lean_dec(v_a_894_);
lean_dec_ref(v_a_893_);
lean_dec(v_a_892_);
lean_dec_ref(v_a_891_);
lean_dec(v_a_890_);
lean_dec(v_a_889_);
lean_dec_ref(v_a_888_);
return v_res_900_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg(lean_object* v_a_901_){
_start:
{
lean_object* v___x_903_; lean_object* v_specBackwardRuleCache_904_; lean_object* v_splitBackwardRuleCache_905_; lean_object* v_latticeBackwardRuleCache_906_; lean_object* v_frameBackwardRuleCache_907_; lean_object* v_frameDB_908_; lean_object* v_invariants_909_; lean_object* v_vcs_910_; lean_object* v_simpState_911_; lean_object* v_fuel_912_; lean_object* v_inlineHandledInvariants_913_; lean_object* v___x_915_; uint8_t v_isShared_916_; uint8_t v_isSharedCheck_938_; 
v___x_903_ = lean_st_ref_take(v_a_901_);
v_specBackwardRuleCache_904_ = lean_ctor_get(v___x_903_, 0);
v_splitBackwardRuleCache_905_ = lean_ctor_get(v___x_903_, 1);
v_latticeBackwardRuleCache_906_ = lean_ctor_get(v___x_903_, 2);
v_frameBackwardRuleCache_907_ = lean_ctor_get(v___x_903_, 3);
v_frameDB_908_ = lean_ctor_get(v___x_903_, 4);
v_invariants_909_ = lean_ctor_get(v___x_903_, 5);
v_vcs_910_ = lean_ctor_get(v___x_903_, 6);
v_simpState_911_ = lean_ctor_get(v___x_903_, 7);
v_fuel_912_ = lean_ctor_get(v___x_903_, 8);
v_inlineHandledInvariants_913_ = lean_ctor_get(v___x_903_, 9);
v_isSharedCheck_938_ = !lean_is_exclusive(v___x_903_);
if (v_isSharedCheck_938_ == 0)
{
v___x_915_ = v___x_903_;
v_isShared_916_ = v_isSharedCheck_938_;
goto v_resetjp_914_;
}
else
{
lean_inc(v_inlineHandledInvariants_913_);
lean_inc(v_fuel_912_);
lean_inc(v_simpState_911_);
lean_inc(v_vcs_910_);
lean_inc(v_invariants_909_);
lean_inc(v_frameDB_908_);
lean_inc(v_frameBackwardRuleCache_907_);
lean_inc(v_latticeBackwardRuleCache_906_);
lean_inc(v_splitBackwardRuleCache_905_);
lean_inc(v_specBackwardRuleCache_904_);
lean_dec(v___x_903_);
v___x_915_ = lean_box(0);
v_isShared_916_ = v_isSharedCheck_938_;
goto v_resetjp_914_;
}
v_resetjp_914_:
{
lean_object* v___x_917_; lean_object* v___y_919_; 
v___x_917_ = lean_box(0);
if (lean_obj_tag(v_fuel_912_) == 0)
{
lean_object* v_n_925_; lean_object* v_zero_926_; uint8_t v_isZero_927_; 
v_n_925_ = lean_ctor_get(v_fuel_912_, 0);
v_zero_926_ = lean_unsigned_to_nat(0u);
v_isZero_927_ = lean_nat_dec_eq(v_n_925_, v_zero_926_);
if (v_isZero_927_ == 0)
{
lean_object* v___x_929_; uint8_t v_isShared_930_; uint8_t v_isSharedCheck_936_; 
lean_inc(v_n_925_);
v_isSharedCheck_936_ = !lean_is_exclusive(v_fuel_912_);
if (v_isSharedCheck_936_ == 0)
{
lean_object* v_unused_937_; 
v_unused_937_ = lean_ctor_get(v_fuel_912_, 0);
lean_dec(v_unused_937_);
v___x_929_ = v_fuel_912_;
v_isShared_930_ = v_isSharedCheck_936_;
goto v_resetjp_928_;
}
else
{
lean_dec(v_fuel_912_);
v___x_929_ = lean_box(0);
v_isShared_930_ = v_isSharedCheck_936_;
goto v_resetjp_928_;
}
v_resetjp_928_:
{
lean_object* v_one_931_; lean_object* v_n_932_; lean_object* v___x_934_; 
v_one_931_ = lean_unsigned_to_nat(1u);
v_n_932_ = lean_nat_sub(v_n_925_, v_one_931_);
lean_dec(v_n_925_);
if (v_isShared_930_ == 0)
{
lean_ctor_set(v___x_929_, 0, v_n_932_);
v___x_934_ = v___x_929_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v_n_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
v___y_919_ = v___x_934_;
goto v___jp_918_;
}
}
}
else
{
v___y_919_ = v_fuel_912_;
goto v___jp_918_;
}
}
else
{
v___y_919_ = v_fuel_912_;
goto v___jp_918_;
}
v___jp_918_:
{
lean_object* v___x_921_; 
if (v_isShared_916_ == 0)
{
lean_ctor_set(v___x_915_, 8, v___y_919_);
v___x_921_ = v___x_915_;
goto v_reusejp_920_;
}
else
{
lean_object* v_reuseFailAlloc_924_; 
v_reuseFailAlloc_924_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_924_, 0, v_specBackwardRuleCache_904_);
lean_ctor_set(v_reuseFailAlloc_924_, 1, v_splitBackwardRuleCache_905_);
lean_ctor_set(v_reuseFailAlloc_924_, 2, v_latticeBackwardRuleCache_906_);
lean_ctor_set(v_reuseFailAlloc_924_, 3, v_frameBackwardRuleCache_907_);
lean_ctor_set(v_reuseFailAlloc_924_, 4, v_frameDB_908_);
lean_ctor_set(v_reuseFailAlloc_924_, 5, v_invariants_909_);
lean_ctor_set(v_reuseFailAlloc_924_, 6, v_vcs_910_);
lean_ctor_set(v_reuseFailAlloc_924_, 7, v_simpState_911_);
lean_ctor_set(v_reuseFailAlloc_924_, 8, v___y_919_);
lean_ctor_set(v_reuseFailAlloc_924_, 9, v_inlineHandledInvariants_913_);
v___x_921_ = v_reuseFailAlloc_924_;
goto v_reusejp_920_;
}
v_reusejp_920_:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = lean_st_ref_put(v_a_901_, v___x_921_);
v___x_923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_923_, 0, v___x_917_);
return v___x_923_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_burnOne___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_901_ = stack[0].m_obj;
lean_object* v_res_939_;
v_res_939_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_901_);
stack->m_obj
 = v_res_939_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___redArg___boxed(lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_940_);
lean_dec(v_a_940_);
return v_res_942_;
}
}
lean_object* l_Lean_Elab_Tactic_VCGen_burnOne(lean_object* v_a_943_, lean_object* v_a_944_, lean_object* v_a_945_, lean_object* v_a_946_, lean_object* v_a_947_, lean_object* v_a_948_, lean_object* v_a_949_, lean_object* v_a_950_, lean_object* v_a_951_, lean_object* v_a_952_, lean_object* v_a_953_){
_start:
{
lean_object* v___x_955_; 
v___x_955_ = l_Lean_Elab_Tactic_VCGen_burnOne___redArg(v_a_944_);
return v___x_955_;
}
}
LEAN_EXPORT void l_Lean_Elab_Tactic_VCGen_burnOne_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_943_ = stack[0].m_obj;
lean_object* v_a_944_ = stack[1].m_obj;
lean_object* v_a_945_ = stack[2].m_obj;
lean_object* v_a_946_ = stack[3].m_obj;
lean_object* v_a_947_ = stack[4].m_obj;
lean_object* v_a_948_ = stack[5].m_obj;
lean_object* v_a_949_ = stack[6].m_obj;
lean_object* v_a_950_ = stack[7].m_obj;
lean_object* v_a_951_ = stack[8].m_obj;
lean_object* v_a_952_ = stack[9].m_obj;
lean_object* v_a_953_ = stack[10].m_obj;
lean_object* v_res_956_;
v_res_956_ = l_Lean_Elab_Tactic_VCGen_burnOne(v_a_943_, v_a_944_, v_a_945_, v_a_946_, v_a_947_, v_a_948_, v_a_949_, v_a_950_, v_a_951_, v_a_952_, v_a_953_);
stack->m_obj
 = v_res_956_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_VCGen_burnOne___boxed(lean_object* v_a_957_, lean_object* v_a_958_, lean_object* v_a_959_, lean_object* v_a_960_, lean_object* v_a_961_, lean_object* v_a_962_, lean_object* v_a_963_, lean_object* v_a_964_, lean_object* v_a_965_, lean_object* v_a_966_, lean_object* v_a_967_, lean_object* v_a_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l_Lean_Elab_Tactic_VCGen_burnOne(v_a_957_, v_a_958_, v_a_959_, v_a_960_, v_a_961_, v_a_962_, v_a_963_, v_a_964_, v_a_965_, v_a_966_, v_a_967_);
lean_dec(v_a_967_);
lean_dec_ref(v_a_966_);
lean_dec(v_a_965_);
lean_dec_ref(v_a_964_);
lean_dec(v_a_963_);
lean_dec_ref(v_a_962_);
lean_dec(v_a_961_);
lean_dec_ref(v_a_960_);
lean_dec(v_a_959_);
lean_dec(v_a_958_);
lean_dec_ref(v_a_957_);
return v_res_969_;
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
