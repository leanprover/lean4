// Lean compiler output
// Module: Lean.Elab.Tactic.Do.Internal.VCGen.Context
// Imports: public import Lean.Elab.Tactic.Do.VCGen.Basic public import Lean.Elab.Tactic.Do.Internal.VCGen.SpecDB public import Lean.Meta.Sym.Apply public import Lean.Meta.Sym.Simp.DiscrTree public import Lean.Meta.Sym.Simp.SimpM public import Lean.Meta.Tactic.Grind.Types
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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
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
size_t lean_usize_shift_left(size_t, size_t);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_deferred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_deferred_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_elaborated_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_elaborated_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__0_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_progTy(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_progTy___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Value(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Value___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_EPred(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_EPred___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx___redArg(lean_object* v_x_1_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
else
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx___redArg___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx___redArg(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx(lean_object* v_00_u03b1_6_, lean_object* v_x_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx___redArg(v_x_7_);
return v___x_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx___boxed(lean_object* v_00_u03b1_9_, lean_object* v_x_10_){
_start:
{
lean_object* v_res_11_; 
v_res_11_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorIdx(v_00_u03b1_9_, v_x_10_);
lean_dec_ref(v_x_10_);
return v_res_11_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___redArg(lean_object* v_t_12_, lean_object* v_k_13_){
_start:
{
if (lean_obj_tag(v_t_12_) == 0)
{
lean_object* v_elabFn_14_; lean_object* v___x_15_; 
v_elabFn_14_ = lean_ctor_get(v_t_12_, 0);
lean_inc_ref(v_elabFn_14_);
lean_dec_ref_known(v_t_12_, 1);
v___x_15_ = lean_apply_1(v_k_13_, v_elabFn_14_);
return v___x_15_;
}
else
{
lean_object* v_value_16_; lean_object* v___x_17_; 
v_value_16_ = lean_ctor_get(v_t_12_, 0);
lean_inc(v_value_16_);
lean_dec_ref_known(v_t_12_, 1);
v___x_17_ = lean_apply_1(v_k_13_, v_value_16_);
return v___x_17_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim(lean_object* v_00_u03b1_18_, lean_object* v_motive_19_, lean_object* v_ctorIdx_20_, lean_object* v_t_21_, lean_object* v_h_22_, lean_object* v_k_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___redArg(v_t_21_, v_k_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___boxed(lean_object* v_00_u03b1_25_, lean_object* v_motive_26_, lean_object* v_ctorIdx_27_, lean_object* v_t_28_, lean_object* v_h_29_, lean_object* v_k_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim(v_00_u03b1_25_, v_motive_26_, v_ctorIdx_27_, v_t_28_, v_h_29_, v_k_30_);
lean_dec(v_ctorIdx_27_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_deferred_elim___redArg(lean_object* v_t_32_, lean_object* v_deferred_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___redArg(v_t_32_, v_deferred_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_deferred_elim(lean_object* v_00_u03b1_35_, lean_object* v_motive_36_, lean_object* v_t_37_, lean_object* v_h_38_, lean_object* v_deferred_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___redArg(v_t_37_, v_deferred_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_elaborated_elim___redArg(lean_object* v_t_41_, lean_object* v_elaborated_42_){
_start:
{
lean_object* v___x_43_; 
v___x_43_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___redArg(v_t_41_, v_elaborated_42_);
return v___x_43_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_elaborated_elim(lean_object* v_00_u03b1_44_, lean_object* v_motive_45_, lean_object* v_t_46_, lean_object* v_h_47_, lean_object* v_elaborated_48_){
_start:
{
lean_object* v___x_49_; 
v___x_49_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_ctorElim___redArg(v_t_46_, v_elaborated_48_);
return v___x_49_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg___lam__0(lean_object* v_toPure_50_, lean_object* v_a_51_, lean_object* v_____r_52_){
_start:
{
lean_object* v___x_53_; 
v___x_53_ = lean_apply_2(v_toPure_50_, lean_box(0), v_a_51_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg___lam__1(lean_object* v_toPure_54_, lean_object* v_writeback_55_, lean_object* v_toBind_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___f_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
lean_inc(v_a_57_);
v___f_58_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg___lam__0), 3, 2);
lean_closure_set(v___f_58_, 0, v_toPure_54_);
lean_closure_set(v___f_58_, 1, v_a_57_);
v___x_59_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_59_, 0, v_a_57_);
v___x_60_ = lean_apply_1(v_writeback_55_, v___x_59_);
v___x_61_ = lean_apply_4(v_toBind_56_, lean_box(0), lean_box(0), v___x_60_, v___f_58_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg(lean_object* v_inst_62_, lean_object* v_inst_63_, lean_object* v_d_64_, lean_object* v_writeback_65_, lean_object* v_m_66_){
_start:
{
lean_object* v_toApplicative_67_; 
v_toApplicative_67_ = lean_ctor_get(v_inst_62_, 0);
lean_inc_ref(v_toApplicative_67_);
if (lean_obj_tag(v_d_64_) == 0)
{
lean_object* v_toBind_68_; lean_object* v_toPure_69_; lean_object* v_elabFn_70_; lean_object* v___f_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; 
v_toBind_68_ = lean_ctor_get(v_inst_62_, 1);
lean_inc_n(v_toBind_68_, 2);
lean_dec_ref(v_inst_62_);
v_toPure_69_ = lean_ctor_get(v_toApplicative_67_, 1);
lean_inc(v_toPure_69_);
lean_dec_ref(v_toApplicative_67_);
v_elabFn_70_ = lean_ctor_get(v_d_64_, 0);
lean_inc_ref(v_elabFn_70_);
lean_dec_ref_known(v_d_64_, 1);
v___f_71_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg___lam__1), 4, 3);
lean_closure_set(v___f_71_, 0, v_toPure_69_);
lean_closure_set(v___f_71_, 1, v_writeback_65_);
lean_closure_set(v___f_71_, 2, v_toBind_68_);
v___x_72_ = lean_apply_1(v_elabFn_70_, v_m_66_);
v___x_73_ = lean_apply_2(v_inst_63_, lean_box(0), v___x_72_);
v___x_74_ = lean_apply_4(v_toBind_68_, lean_box(0), lean_box(0), v___x_73_, v___f_71_);
return v___x_74_;
}
else
{
lean_object* v_toPure_75_; lean_object* v_value_76_; lean_object* v___x_77_; 
lean_dec_ref(v_m_66_);
lean_dec(v_writeback_65_);
lean_dec(v_inst_63_);
lean_dec_ref(v_inst_62_);
v_toPure_75_ = lean_ctor_get(v_toApplicative_67_, 1);
lean_inc(v_toPure_75_);
lean_dec_ref(v_toApplicative_67_);
v_value_76_ = lean_ctor_get(v_d_64_, 0);
lean_inc(v_value_76_);
lean_dec_ref_known(v_d_64_, 1);
v___x_77_ = lean_apply_2(v_toPure_75_, lean_box(0), v_value_76_);
return v___x_77_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_Deferred_force(lean_object* v_00_u03b1_78_, lean_object* v_n_79_, lean_object* v_inst_80_, lean_object* v_inst_81_, lean_object* v_d_82_, lean_object* v_writeback_83_, lean_object* v_m_84_){
_start:
{
lean_object* v___x_85_; 
v___x_85_ = l_Lean_Elab_Tactic_Do_Internal_Deferred_force___redArg(v_inst_80_, v_inst_81_, v_d_82_, v_writeback_83_, v_m_84_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1(void){
_start:
{
uint8_t v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; 
v___x_88_ = 0;
v___x_89_ = lean_unsigned_to_nat(0u);
v___x_90_ = lean_box(0);
v___x_91_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__0));
v___x_92_ = l_Lean_Meta_Sym_instInhabitedPattern_default;
v___x_93_ = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(v___x_93_, 0, v___x_92_);
lean_ctor_set(v___x_93_, 1, v___x_91_);
lean_ctor_set(v___x_93_, 2, v___x_90_);
lean_ctor_set(v___x_93_, 3, v___x_89_);
lean_ctor_set_uint8(v___x_93_, sizeof(void*)*4, v___x_88_);
return v___x_93_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default(void){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1, &l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1_once, _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default___closed__1);
return v___x_94_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry(void){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_Lean_Elab_Tactic_Do_Internal_instInhabitedFrameEntry_default;
return v___x_95_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_progTy(lean_object* v_info_96_){
_start:
{
lean_object* v_args_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; 
v_args_97_ = lean_ctor_get(v_info_96_, 1);
v___x_98_ = l_Lean_instInhabitedExpr;
v___x_99_ = lean_unsigned_to_nat(0u);
v___x_100_ = lean_array_get_borrowed(v___x_98_, v_args_97_, v___x_99_);
lean_inc(v___x_100_);
return v___x_100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_progTy___boxed(lean_object* v_info_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_progTy(v_info_101_);
lean_dec_ref(v_info_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(lean_object* v_info_103_){
_start:
{
lean_object* v_args_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; 
v_args_104_ = lean_ctor_get(v_info_103_, 1);
v___x_105_ = l_Lean_instInhabitedExpr;
v___x_106_ = lean_unsigned_to_nat(0u);
v___x_107_ = lean_array_get_borrowed(v___x_105_, v_args_104_, v___x_106_);
v___x_108_ = l_Lean_Expr_isApp(v___x_107_);
if (v___x_108_ == 0)
{
lean_inc(v___x_107_);
return v___x_107_;
}
else
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Expr_appFn_x21(v___x_107_);
return v___x_109_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m___boxed(lean_object* v_info_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_110_);
lean_dec_ref(v_info_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Value(lean_object* v_info_112_){
_start:
{
lean_object* v_args_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; 
v_args_113_ = lean_ctor_get(v_info_112_, 1);
v___x_114_ = l_Lean_instInhabitedExpr;
v___x_115_ = lean_unsigned_to_nat(1u);
v___x_116_ = lean_array_get_borrowed(v___x_114_, v_args_113_, v___x_115_);
lean_inc(v___x_116_);
return v___x_116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Value___boxed(lean_object* v_info_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Value(v_info_117_);
lean_dec_ref(v_info_117_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(lean_object* v_info_119_){
_start:
{
lean_object* v_args_120_; lean_object* v___x_121_; lean_object* v___x_122_; lean_object* v___x_123_; 
v_args_120_ = lean_ctor_get(v_info_119_, 1);
v___x_121_ = l_Lean_instInhabitedExpr;
v___x_122_ = lean_unsigned_to_nat(2u);
v___x_123_ = lean_array_get_borrowed(v___x_121_, v_args_120_, v___x_122_);
lean_inc(v___x_123_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred___boxed(lean_object* v_info_124_){
_start:
{
lean_object* v_res_125_; 
v_res_125_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_124_);
lean_dec_ref(v_info_124_);
return v_res_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_EPred(lean_object* v_info_126_){
_start:
{
lean_object* v_args_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_args_127_ = lean_ctor_get(v_info_126_, 1);
v___x_128_ = l_Lean_instInhabitedExpr;
v___x_129_ = lean_unsigned_to_nat(3u);
v___x_130_ = lean_array_get_borrowed(v___x_128_, v_args_127_, v___x_129_);
lean_inc(v___x_130_);
return v___x_130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_EPred___boxed(lean_object* v_info_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_EPred(v_info_131_);
lean_dec_ref(v_info_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(lean_object* v_info_133_){
_start:
{
lean_object* v_args_134_; lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; 
v_args_134_ = lean_ctor_get(v_info_133_, 1);
v___x_135_ = l_Lean_instInhabitedExpr;
v___x_136_ = lean_unsigned_to_nat(6u);
v___x_137_ = lean_array_get_borrowed(v___x_135_, v_args_134_, v___x_136_);
lean_inc(v___x_137_);
return v___x_137_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP___boxed(lean_object* v_info_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_138_);
lean_dec_ref(v_info_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(lean_object* v_info_140_){
_start:
{
lean_object* v_args_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_args_141_ = lean_ctor_get(v_info_140_, 1);
v___x_142_ = l_Lean_instInhabitedExpr;
v___x_143_ = lean_unsigned_to_nat(7u);
v___x_144_ = lean_array_get_borrowed(v___x_142_, v_args_141_, v___x_143_);
lean_inc(v___x_144_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog___boxed(lean_object* v_info_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_145_);
lean_dec_ref(v_info_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_209_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5));
v___x_210_ = lean_box(0);
v___x_211_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_209_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_211_) == 0)
{
lean_object* v_a_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v_a_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc(v_a_212_);
lean_dec_ref_known(v___x_211_, 1);
v___x_213_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9));
v___x_214_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_213_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_214_) == 0)
{
lean_object* v_a_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v_a_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_a_215_);
lean_dec_ref_known(v___x_214_, 1);
v___x_216_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11));
v___x_217_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_216_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_217_) == 0)
{
lean_object* v_a_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_a_218_ = lean_ctor_get(v___x_217_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v___x_217_, 1);
v___x_219_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13));
v___x_220_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_219_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_220_) == 0)
{
lean_object* v_a_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_a_221_ = lean_ctor_get(v___x_220_, 0);
lean_inc(v_a_221_);
lean_dec_ref_known(v___x_220_, 1);
v___x_222_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15));
v___x_223_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_222_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_223_) == 0)
{
lean_object* v_a_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_a_224_ = lean_ctor_get(v___x_223_, 0);
lean_inc(v_a_224_);
lean_dec_ref_known(v___x_223_, 1);
v___x_225_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17));
v___x_226_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_225_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_226_) == 0)
{
lean_object* v_a_227_; lean_object* v___x_228_; lean_object* v___x_229_; 
v_a_227_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_a_227_);
lean_dec_ref_known(v___x_226_, 1);
v___x_228_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19));
v___x_229_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_228_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_229_) == 0)
{
lean_object* v_a_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_a_230_ = lean_ctor_get(v___x_229_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v___x_229_, 1);
v___x_231_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22));
v___x_232_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_231_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v_a_233_; lean_object* v___x_234_; lean_object* v___x_235_; 
v_a_233_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_a_233_);
lean_dec_ref_known(v___x_232_, 1);
v___x_234_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__25));
v___x_235_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_234_, v___x_210_, v_a_204_, v_a_205_, v_a_206_, v_a_207_);
if (lean_obj_tag(v___x_235_) == 0)
{
lean_object* v_a_236_; lean_object* v___x_238_; uint8_t v_isShared_239_; uint8_t v_isSharedCheck_244_; 
v_a_236_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_244_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_244_ == 0)
{
v___x_238_ = v___x_235_;
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
else
{
lean_inc(v_a_236_);
lean_dec(v___x_235_);
v___x_238_ = lean_box(0);
v_isShared_239_ = v_isSharedCheck_244_;
goto v_resetjp_237_;
}
v_resetjp_237_:
{
lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_240_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_240_, 0, v_a_212_);
lean_ctor_set(v___x_240_, 1, v_a_215_);
lean_ctor_set(v___x_240_, 2, v_a_218_);
lean_ctor_set(v___x_240_, 3, v_a_221_);
lean_ctor_set(v___x_240_, 4, v_a_224_);
lean_ctor_set(v___x_240_, 5, v_a_227_);
lean_ctor_set(v___x_240_, 6, v_a_230_);
lean_ctor_set(v___x_240_, 7, v_a_233_);
lean_ctor_set(v___x_240_, 8, v_a_236_);
if (v_isShared_239_ == 0)
{
lean_ctor_set(v___x_238_, 0, v___x_240_);
v___x_242_ = v___x_238_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
else
{
lean_object* v_a_245_; lean_object* v___x_247_; uint8_t v_isShared_248_; uint8_t v_isSharedCheck_252_; 
lean_dec(v_a_233_);
lean_dec(v_a_230_);
lean_dec(v_a_227_);
lean_dec(v_a_224_);
lean_dec(v_a_221_);
lean_dec(v_a_218_);
lean_dec(v_a_215_);
lean_dec(v_a_212_);
v_a_245_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_252_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_252_ == 0)
{
v___x_247_ = v___x_235_;
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
else
{
lean_inc(v_a_245_);
lean_dec(v___x_235_);
v___x_247_ = lean_box(0);
v_isShared_248_ = v_isSharedCheck_252_;
goto v_resetjp_246_;
}
v_resetjp_246_:
{
lean_object* v___x_250_; 
if (v_isShared_248_ == 0)
{
v___x_250_ = v___x_247_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_a_245_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
else
{
lean_object* v_a_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_260_; 
lean_dec(v_a_230_);
lean_dec(v_a_227_);
lean_dec(v_a_224_);
lean_dec(v_a_221_);
lean_dec(v_a_218_);
lean_dec(v_a_215_);
lean_dec(v_a_212_);
v_a_253_ = lean_ctor_get(v___x_232_, 0);
v_isSharedCheck_260_ = !lean_is_exclusive(v___x_232_);
if (v_isSharedCheck_260_ == 0)
{
v___x_255_ = v___x_232_;
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_a_253_);
lean_dec(v___x_232_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_260_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
lean_object* v___x_258_; 
if (v_isShared_256_ == 0)
{
v___x_258_ = v___x_255_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_a_253_);
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
else
{
lean_object* v_a_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_268_; 
lean_dec(v_a_227_);
lean_dec(v_a_224_);
lean_dec(v_a_221_);
lean_dec(v_a_218_);
lean_dec(v_a_215_);
lean_dec(v_a_212_);
v_a_261_ = lean_ctor_get(v___x_229_, 0);
v_isSharedCheck_268_ = !lean_is_exclusive(v___x_229_);
if (v_isSharedCheck_268_ == 0)
{
v___x_263_ = v___x_229_;
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_a_261_);
lean_dec(v___x_229_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_268_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_266_; 
if (v_isShared_264_ == 0)
{
v___x_266_ = v___x_263_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v_a_261_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
else
{
lean_object* v_a_269_; lean_object* v___x_271_; uint8_t v_isShared_272_; uint8_t v_isSharedCheck_276_; 
lean_dec(v_a_224_);
lean_dec(v_a_221_);
lean_dec(v_a_218_);
lean_dec(v_a_215_);
lean_dec(v_a_212_);
v_a_269_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_276_ == 0)
{
v___x_271_ = v___x_226_;
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
else
{
lean_inc(v_a_269_);
lean_dec(v___x_226_);
v___x_271_ = lean_box(0);
v_isShared_272_ = v_isSharedCheck_276_;
goto v_resetjp_270_;
}
v_resetjp_270_:
{
lean_object* v___x_274_; 
if (v_isShared_272_ == 0)
{
v___x_274_ = v___x_271_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_a_269_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
else
{
lean_object* v_a_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_284_; 
lean_dec(v_a_221_);
lean_dec(v_a_218_);
lean_dec(v_a_215_);
lean_dec(v_a_212_);
v_a_277_ = lean_ctor_get(v___x_223_, 0);
v_isSharedCheck_284_ = !lean_is_exclusive(v___x_223_);
if (v_isSharedCheck_284_ == 0)
{
v___x_279_ = v___x_223_;
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_a_277_);
lean_dec(v___x_223_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_284_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_282_; 
if (v_isShared_280_ == 0)
{
v___x_282_ = v___x_279_;
goto v_reusejp_281_;
}
else
{
lean_object* v_reuseFailAlloc_283_; 
v_reuseFailAlloc_283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_283_, 0, v_a_277_);
v___x_282_ = v_reuseFailAlloc_283_;
goto v_reusejp_281_;
}
v_reusejp_281_:
{
return v___x_282_;
}
}
}
}
else
{
lean_object* v_a_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_292_; 
lean_dec(v_a_218_);
lean_dec(v_a_215_);
lean_dec(v_a_212_);
v_a_285_ = lean_ctor_get(v___x_220_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_220_);
if (v_isSharedCheck_292_ == 0)
{
v___x_287_ = v___x_220_;
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_a_285_);
lean_dec(v___x_220_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_292_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_290_; 
if (v_isShared_288_ == 0)
{
v___x_290_ = v___x_287_;
goto v_reusejp_289_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v_a_285_);
v___x_290_ = v_reuseFailAlloc_291_;
goto v_reusejp_289_;
}
v_reusejp_289_:
{
return v___x_290_;
}
}
}
}
else
{
lean_object* v_a_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_300_; 
lean_dec(v_a_215_);
lean_dec(v_a_212_);
v_a_293_ = lean_ctor_get(v___x_217_, 0);
v_isSharedCheck_300_ = !lean_is_exclusive(v___x_217_);
if (v_isSharedCheck_300_ == 0)
{
v___x_295_ = v___x_217_;
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_a_293_);
lean_dec(v___x_217_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_300_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v___x_298_; 
if (v_isShared_296_ == 0)
{
v___x_298_ = v___x_295_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v_a_293_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
return v___x_298_;
}
}
}
}
else
{
lean_object* v_a_301_; lean_object* v___x_303_; uint8_t v_isShared_304_; uint8_t v_isSharedCheck_308_; 
lean_dec(v_a_212_);
v_a_301_ = lean_ctor_get(v___x_214_, 0);
v_isSharedCheck_308_ = !lean_is_exclusive(v___x_214_);
if (v_isSharedCheck_308_ == 0)
{
v___x_303_ = v___x_214_;
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
else
{
lean_inc(v_a_301_);
lean_dec(v___x_214_);
v___x_303_ = lean_box(0);
v_isShared_304_ = v_isSharedCheck_308_;
goto v_resetjp_302_;
}
v_resetjp_302_:
{
lean_object* v___x_306_; 
if (v_isShared_304_ == 0)
{
v___x_306_ = v___x_303_;
goto v_reusejp_305_;
}
else
{
lean_object* v_reuseFailAlloc_307_; 
v_reuseFailAlloc_307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_307_, 0, v_a_301_);
v___x_306_ = v_reuseFailAlloc_307_;
goto v_reusejp_305_;
}
v_reusejp_305_:
{
return v___x_306_;
}
}
}
}
else
{
lean_object* v_a_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_316_; 
v_a_309_ = lean_ctor_get(v___x_211_, 0);
v_isSharedCheck_316_ = !lean_is_exclusive(v___x_211_);
if (v_isSharedCheck_316_ == 0)
{
v___x_311_ = v___x_211_;
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_a_309_);
lean_dec(v___x_211_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_316_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_314_; 
if (v_isShared_312_ == 0)
{
v___x_314_ = v___x_311_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_a_309_);
v___x_314_ = v_reuseFailAlloc_315_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
return v___x_314_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___boxed(lean_object* v_a_317_, lean_object* v_a_318_, lean_object* v_a_319_, lean_object* v_a_320_, lean_object* v_a_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(v_a_317_, v_a_318_, v_a_319_, v_a_320_);
lean_dec(v_a_320_);
lean_dec_ref(v_a_319_);
lean_dec(v_a_318_);
lean_dec_ref(v_a_317_);
return v_res_322_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_323_ = lean_unsigned_to_nat(0u);
v___x_324_ = lean_box(0);
v___x_325_ = lean_box(1);
v___x_326_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default;
v___x_327_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_327_, 0, v___x_326_);
lean_ctor_set(v___x_327_, 1, v___x_325_);
lean_ctor_set(v___x_327_, 2, v___x_324_);
lean_ctor_set(v___x_327_, 3, v___x_323_);
return v___x_327_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default(void){
_start:
{
lean_object* v___x_328_; 
v___x_328_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0);
return v___x_328_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope(void){
_start:
{
lean_object* v___x_329_; 
v___x_329_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default;
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_registerJP(lean_object* v_s_330_, lean_object* v_fv_331_, lean_object* v_info_332_){
_start:
{
lean_object* v_specs_333_; lean_object* v_jps_334_; lean_object* v_lastLiftedPre_x3f_335_; lean_object* v_nextDeclIdx_336_; lean_object* v___x_338_; uint8_t v_isShared_339_; uint8_t v_isSharedCheck_344_; 
v_specs_333_ = lean_ctor_get(v_s_330_, 0);
v_jps_334_ = lean_ctor_get(v_s_330_, 1);
v_lastLiftedPre_x3f_335_ = lean_ctor_get(v_s_330_, 2);
v_nextDeclIdx_336_ = lean_ctor_get(v_s_330_, 3);
v_isSharedCheck_344_ = !lean_is_exclusive(v_s_330_);
if (v_isSharedCheck_344_ == 0)
{
v___x_338_ = v_s_330_;
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
else
{
lean_inc(v_nextDeclIdx_336_);
lean_inc(v_lastLiftedPre_x3f_335_);
lean_inc(v_jps_334_);
lean_inc(v_specs_333_);
lean_dec(v_s_330_);
v___x_338_ = lean_box(0);
v_isShared_339_ = v_isSharedCheck_344_;
goto v_resetjp_337_;
}
v_resetjp_337_:
{
lean_object* v___x_340_; lean_object* v___x_342_; 
v___x_340_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_331_, v_info_332_, v_jps_334_);
if (v_isShared_339_ == 0)
{
lean_ctor_set(v___x_338_, 1, v___x_340_);
v___x_342_ = v___x_338_;
goto v_reusejp_341_;
}
else
{
lean_object* v_reuseFailAlloc_343_; 
v_reuseFailAlloc_343_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_343_, 0, v_specs_333_);
lean_ctor_set(v_reuseFailAlloc_343_, 1, v___x_340_);
lean_ctor_set(v_reuseFailAlloc_343_, 2, v_lastLiftedPre_x3f_335_);
lean_ctor_set(v_reuseFailAlloc_343_, 3, v_nextDeclIdx_336_);
v___x_342_ = v_reuseFailAlloc_343_;
goto v_reusejp_341_;
}
v_reusejp_341_:
{
return v___x_342_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(lean_object* v_t_345_, lean_object* v_k_346_){
_start:
{
if (lean_obj_tag(v_t_345_) == 0)
{
lean_object* v_k_347_; lean_object* v_v_348_; lean_object* v_l_349_; lean_object* v_r_350_; uint8_t v___x_351_; 
v_k_347_ = lean_ctor_get(v_t_345_, 1);
v_v_348_ = lean_ctor_get(v_t_345_, 2);
v_l_349_ = lean_ctor_get(v_t_345_, 3);
v_r_350_ = lean_ctor_get(v_t_345_, 4);
v___x_351_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_346_, v_k_347_);
switch(v___x_351_)
{
case 0:
{
v_t_345_ = v_l_349_;
goto _start;
}
case 1:
{
lean_object* v___x_353_; 
lean_inc(v_v_348_);
v___x_353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_353_, 0, v_v_348_);
return v___x_353_;
}
default: 
{
v_t_345_ = v_r_350_;
goto _start;
}
}
}
else
{
lean_object* v___x_355_; 
v___x_355_ = lean_box(0);
return v___x_355_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_356_, lean_object* v_k_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_356_, v_k_357_);
lean_dec(v_k_357_);
lean_dec(v_t_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(lean_object* v_s_359_, lean_object* v_fv_360_){
_start:
{
lean_object* v_jps_361_; lean_object* v___x_362_; 
v_jps_361_ = lean_ctor_get(v_s_359_, 1);
v___x_362_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_jps_361_, v_fv_360_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f___boxed(lean_object* v_s_363_, lean_object* v_fv_364_){
_start:
{
lean_object* v_res_365_; 
v_res_365_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(v_s_363_, v_fv_364_);
lean_dec(v_fv_364_);
lean_dec_ref(v_s_363_);
return v_res_365_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(lean_object* v_00_u03b4_366_, lean_object* v_t_367_, lean_object* v_k_368_){
_start:
{
lean_object* v___x_369_; 
v___x_369_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_367_, v_k_368_);
return v___x_369_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_370_, lean_object* v_t_371_, lean_object* v_k_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(v_00_u03b4_370_, v_t_371_, v_k_372_);
lean_dec(v_k_372_);
lean_dec(v_t_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(lean_object* v_s_374_, lean_object* v_thm_375_){
_start:
{
lean_object* v_specs_376_; lean_object* v_jps_377_; lean_object* v_lastLiftedPre_x3f_378_; lean_object* v_nextDeclIdx_379_; lean_object* v___x_381_; uint8_t v_isShared_382_; uint8_t v_isSharedCheck_387_; 
v_specs_376_ = lean_ctor_get(v_s_374_, 0);
v_jps_377_ = lean_ctor_get(v_s_374_, 1);
v_lastLiftedPre_x3f_378_ = lean_ctor_get(v_s_374_, 2);
v_nextDeclIdx_379_ = lean_ctor_get(v_s_374_, 3);
v_isSharedCheck_387_ = !lean_is_exclusive(v_s_374_);
if (v_isSharedCheck_387_ == 0)
{
v___x_381_ = v_s_374_;
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
else
{
lean_inc(v_nextDeclIdx_379_);
lean_inc(v_lastLiftedPre_x3f_378_);
lean_inc(v_jps_377_);
lean_inc(v_specs_376_);
lean_dec(v_s_374_);
v___x_381_ = lean_box(0);
v_isShared_382_ = v_isSharedCheck_387_;
goto v_resetjp_380_;
}
v_resetjp_380_:
{
lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_383_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(v_specs_376_, v_thm_375_);
if (v_isShared_382_ == 0)
{
lean_ctor_set(v___x_381_, 0, v___x_383_);
v___x_385_ = v___x_381_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
lean_ctor_set(v_reuseFailAlloc_386_, 1, v_jps_377_);
lean_ctor_set(v_reuseFailAlloc_386_, 2, v_lastLiftedPre_x3f_378_);
lean_ctor_set(v_reuseFailAlloc_386_, 3, v_nextDeclIdx_379_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object* v_x_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_, lean_object* v___y_392_, lean_object* v___y_393_, lean_object* v___y_394_, lean_object* v___y_395_, lean_object* v___y_396_, lean_object* v___y_397_, lean_object* v___y_398_, lean_object* v___y_399_){
_start:
{
lean_object* v___x_401_; 
lean_inc(v___y_395_);
lean_inc_ref(v___y_394_);
lean_inc(v___y_393_);
lean_inc_ref(v___y_392_);
lean_inc(v___y_391_);
lean_inc(v___y_390_);
lean_inc_ref(v___y_389_);
v___x_401_ = lean_apply_12(v_x_388_, v___y_389_, v___y_390_, v___y_391_, v___y_392_, v___y_393_, v___y_394_, v___y_395_, v___y_396_, v___y_397_, v___y_398_, v___y_399_, lean_box(0));
return v___x_401_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object* v_x_402_, lean_object* v___y_403_, lean_object* v___y_404_, lean_object* v___y_405_, lean_object* v___y_406_, lean_object* v___y_407_, lean_object* v___y_408_, lean_object* v___y_409_, lean_object* v___y_410_, lean_object* v___y_411_, lean_object* v___y_412_, lean_object* v___y_413_, lean_object* v___y_414_){
_start:
{
lean_object* v_res_415_; 
v_res_415_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_402_, v___y_403_, v___y_404_, v___y_405_, v___y_406_, v___y_407_, v___y_408_, v___y_409_, v___y_410_, v___y_411_, v___y_412_, v___y_413_);
lean_dec(v___y_409_);
lean_dec_ref(v___y_408_);
lean_dec(v___y_407_);
lean_dec_ref(v___y_406_);
lean_dec(v___y_405_);
lean_dec(v___y_404_);
lean_dec_ref(v___y_403_);
return v_res_415_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object* v_mvarId_416_, lean_object* v_x_417_, lean_object* v___y_418_, lean_object* v___y_419_, lean_object* v___y_420_, lean_object* v___y_421_, lean_object* v___y_422_, lean_object* v___y_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_, lean_object* v___y_428_){
_start:
{
lean_object* v___f_430_; lean_object* v___x_431_; 
lean_inc(v___y_424_);
lean_inc_ref(v___y_423_);
lean_inc(v___y_422_);
lean_inc_ref(v___y_421_);
lean_inc(v___y_420_);
lean_inc(v___y_419_);
lean_inc_ref(v___y_418_);
v___f_430_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_430_, 0, v_x_417_);
lean_closure_set(v___f_430_, 1, v___y_418_);
lean_closure_set(v___f_430_, 2, v___y_419_);
lean_closure_set(v___f_430_, 3, v___y_420_);
lean_closure_set(v___f_430_, 4, v___y_421_);
lean_closure_set(v___f_430_, 5, v___y_422_);
lean_closure_set(v___f_430_, 6, v___y_423_);
lean_closure_set(v___f_430_, 7, v___y_424_);
v___x_431_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_416_, v___f_430_, v___y_425_, v___y_426_, v___y_427_, v___y_428_);
if (lean_obj_tag(v___x_431_) == 0)
{
return v___x_431_;
}
else
{
lean_object* v_a_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_439_; 
v_a_432_ = lean_ctor_get(v___x_431_, 0);
v_isSharedCheck_439_ = !lean_is_exclusive(v___x_431_);
if (v_isSharedCheck_439_ == 0)
{
v___x_434_ = v___x_431_;
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_a_432_);
lean_dec(v___x_431_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_439_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_437_; 
if (v_isShared_435_ == 0)
{
v___x_437_ = v___x_434_;
goto v_reusejp_436_;
}
else
{
lean_object* v_reuseFailAlloc_438_; 
v_reuseFailAlloc_438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_438_, 0, v_a_432_);
v___x_437_ = v_reuseFailAlloc_438_;
goto v_reusejp_436_;
}
v_reusejp_436_:
{
return v___x_437_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object* v_mvarId_440_, lean_object* v_x_441_, lean_object* v___y_442_, lean_object* v___y_443_, lean_object* v___y_444_, lean_object* v___y_445_, lean_object* v___y_446_, lean_object* v___y_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_440_, v_x_441_, v___y_442_, v___y_443_, v___y_444_, v___y_445_, v___y_446_, v___y_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_, v___y_452_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
lean_dec(v___y_450_);
lean_dec_ref(v___y_449_);
lean_dec(v___y_448_);
lean_dec_ref(v___y_447_);
lean_dec(v___y_446_);
lean_dec_ref(v___y_445_);
lean_dec(v___y_444_);
lean_dec(v___y_443_);
lean_dec_ref(v___y_442_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(lean_object* v_00_u03b1_455_, lean_object* v_mvarId_456_, lean_object* v_x_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_, lean_object* v___y_467_, lean_object* v___y_468_){
_start:
{
lean_object* v___x_470_; 
v___x_470_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_456_, v_x_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_, v___y_467_, v___y_468_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object* v_00_u03b1_471_, lean_object* v_mvarId_472_, lean_object* v_x_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_471_, v_mvarId_472_, v_x_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_);
lean_dec(v___y_484_);
lean_dec_ref(v___y_483_);
lean_dec(v___y_482_);
lean_dec_ref(v___y_481_);
lean_dec(v___y_480_);
lean_dec_ref(v___y_479_);
lean_dec(v___y_478_);
lean_dec_ref(v___y_477_);
lean_dec(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object* v_as_487_, size_t v_i_488_, size_t v_stop_489_, lean_object* v_b_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_){
_start:
{
lean_object* v_a_497_; uint8_t v___x_501_; 
v___x_501_ = lean_usize_dec_eq(v_i_488_, v_stop_489_);
if (v___x_501_ == 0)
{
lean_object* v___x_502_; 
v___x_502_ = lean_array_uget_borrowed(v_as_487_, v_i_488_);
if (lean_obj_tag(v___x_502_) == 0)
{
v_a_497_ = v_b_490_;
goto v___jp_496_;
}
else
{
lean_object* v_val_503_; uint8_t v___x_504_; 
v_val_503_ = lean_ctor_get(v___x_502_, 0);
v___x_504_ = l_Lean_LocalDecl_isAuxDecl(v_val_503_);
if (v___x_504_ == 0)
{
lean_object* v___x_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_505_ = l_Lean_LocalDecl_fvarId(v_val_503_);
v___x_506_ = lean_unsigned_to_nat(100u);
v___x_507_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(v___x_505_, v___x_506_, v___y_491_, v___y_492_, v___y_493_, v___y_494_);
if (lean_obj_tag(v___x_507_) == 0)
{
lean_object* v_a_508_; 
v_a_508_ = lean_ctor_get(v___x_507_, 0);
lean_inc(v_a_508_);
lean_dec_ref_known(v___x_507_, 1);
if (lean_obj_tag(v_a_508_) == 1)
{
lean_object* v_val_509_; lean_object* v___x_510_; 
v_val_509_ = lean_ctor_get(v_a_508_, 0);
lean_inc(v_val_509_);
lean_dec_ref_known(v_a_508_, 1);
v___x_510_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(v_b_490_, v_val_509_);
v_a_497_ = v___x_510_;
goto v___jp_496_;
}
else
{
lean_dec(v_a_508_);
v_a_497_ = v_b_490_;
goto v___jp_496_;
}
}
else
{
lean_object* v_a_511_; lean_object* v___x_513_; uint8_t v_isShared_514_; uint8_t v_isSharedCheck_522_; 
v_a_511_ = lean_ctor_get(v___x_507_, 0);
v_isSharedCheck_522_ = !lean_is_exclusive(v___x_507_);
if (v_isSharedCheck_522_ == 0)
{
v___x_513_ = v___x_507_;
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
else
{
lean_inc(v_a_511_);
lean_dec(v___x_507_);
v___x_513_ = lean_box(0);
v_isShared_514_ = v_isSharedCheck_522_;
goto v_resetjp_512_;
}
v_resetjp_512_:
{
uint8_t v___y_516_; uint8_t v___x_520_; 
v___x_520_ = l_Lean_Exception_isInterrupt(v_a_511_);
if (v___x_520_ == 0)
{
uint8_t v___x_521_; 
lean_inc(v_a_511_);
v___x_521_ = l_Lean_Exception_isRuntime(v_a_511_);
v___y_516_ = v___x_521_;
goto v___jp_515_;
}
else
{
v___y_516_ = v___x_520_;
goto v___jp_515_;
}
v___jp_515_:
{
if (v___y_516_ == 0)
{
lean_del_object(v___x_513_);
lean_dec(v_a_511_);
v_a_497_ = v_b_490_;
goto v___jp_496_;
}
else
{
lean_object* v___x_518_; 
lean_dec_ref(v_b_490_);
if (v_isShared_514_ == 0)
{
v___x_518_ = v___x_513_;
goto v_reusejp_517_;
}
else
{
lean_object* v_reuseFailAlloc_519_; 
v_reuseFailAlloc_519_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_519_, 0, v_a_511_);
v___x_518_ = v_reuseFailAlloc_519_;
goto v_reusejp_517_;
}
v_reusejp_517_:
{
return v___x_518_;
}
}
}
}
}
}
else
{
v_a_497_ = v_b_490_;
goto v___jp_496_;
}
}
}
else
{
lean_object* v___x_523_; 
v___x_523_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_523_, 0, v_b_490_);
return v___x_523_;
}
v___jp_496_:
{
size_t v___x_498_; size_t v___x_499_; 
v___x_498_ = ((size_t)1ULL);
v___x_499_ = lean_usize_add(v_i_488_, v___x_498_);
v_i_488_ = v___x_499_;
v_b_490_ = v_a_497_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_as_524_, lean_object* v_i_525_, lean_object* v_stop_526_, lean_object* v_b_527_, lean_object* v___y_528_, lean_object* v___y_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_){
_start:
{
size_t v_i_boxed_533_; size_t v_stop_boxed_534_; lean_object* v_res_535_; 
v_i_boxed_533_ = lean_unbox_usize(v_i_525_);
lean_dec(v_i_525_);
v_stop_boxed_534_ = lean_unbox_usize(v_stop_526_);
lean_dec(v_stop_526_);
v_res_535_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_524_, v_i_boxed_533_, v_stop_boxed_534_, v_b_527_, v___y_528_, v___y_529_, v___y_530_, v___y_531_);
lean_dec(v___y_531_);
lean_dec_ref(v___y_530_);
lean_dec(v___y_529_);
lean_dec_ref(v___y_528_);
lean_dec_ref(v_as_524_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object* v_x_536_, lean_object* v_x_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_, lean_object* v___y_542_, lean_object* v___y_543_, lean_object* v___y_544_, lean_object* v___y_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_){
_start:
{
if (lean_obj_tag(v_x_536_) == 0)
{
lean_object* v_cs_550_; lean_object* v___x_552_; uint8_t v_isShared_553_; uint8_t v_isSharedCheck_570_; 
v_cs_550_ = lean_ctor_get(v_x_536_, 0);
v_isSharedCheck_570_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_570_ == 0)
{
v___x_552_ = v_x_536_;
v_isShared_553_ = v_isSharedCheck_570_;
goto v_resetjp_551_;
}
else
{
lean_inc(v_cs_550_);
lean_dec(v_x_536_);
v___x_552_ = lean_box(0);
v_isShared_553_ = v_isSharedCheck_570_;
goto v_resetjp_551_;
}
v_resetjp_551_:
{
lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_554_ = lean_unsigned_to_nat(0u);
v___x_555_ = lean_array_get_size(v_cs_550_);
v___x_556_ = lean_nat_dec_lt(v___x_554_, v___x_555_);
if (v___x_556_ == 0)
{
lean_object* v___x_558_; 
lean_dec_ref(v_cs_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v_x_537_);
v___x_558_ = v___x_552_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_x_537_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
else
{
uint8_t v___x_560_; 
v___x_560_ = lean_nat_dec_le(v___x_555_, v___x_555_);
if (v___x_560_ == 0)
{
if (v___x_556_ == 0)
{
lean_object* v___x_562_; 
lean_dec_ref(v_cs_550_);
if (v_isShared_553_ == 0)
{
lean_ctor_set(v___x_552_, 0, v_x_537_);
v___x_562_ = v___x_552_;
goto v_reusejp_561_;
}
else
{
lean_object* v_reuseFailAlloc_563_; 
v_reuseFailAlloc_563_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_563_, 0, v_x_537_);
v___x_562_ = v_reuseFailAlloc_563_;
goto v_reusejp_561_;
}
v_reusejp_561_:
{
return v___x_562_;
}
}
else
{
size_t v___x_564_; size_t v___x_565_; lean_object* v___x_566_; 
lean_del_object(v___x_552_);
v___x_564_ = ((size_t)0ULL);
v___x_565_ = lean_usize_of_nat(v___x_555_);
v___x_566_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_550_, v___x_564_, v___x_565_, v_x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec_ref(v_cs_550_);
return v___x_566_;
}
}
else
{
size_t v___x_567_; size_t v___x_568_; lean_object* v___x_569_; 
lean_del_object(v___x_552_);
v___x_567_ = ((size_t)0ULL);
v___x_568_ = lean_usize_of_nat(v___x_555_);
v___x_569_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_550_, v___x_567_, v___x_568_, v_x_537_, v___y_538_, v___y_539_, v___y_540_, v___y_541_, v___y_542_, v___y_543_, v___y_544_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec_ref(v_cs_550_);
return v___x_569_;
}
}
}
}
else
{
lean_object* v_vs_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_591_; 
v_vs_571_ = lean_ctor_get(v_x_536_, 0);
v_isSharedCheck_591_ = !lean_is_exclusive(v_x_536_);
if (v_isSharedCheck_591_ == 0)
{
v___x_573_ = v_x_536_;
v_isShared_574_ = v_isSharedCheck_591_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_vs_571_);
lean_dec(v_x_536_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_591_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; lean_object* v___x_576_; uint8_t v___x_577_; 
v___x_575_ = lean_unsigned_to_nat(0u);
v___x_576_ = lean_array_get_size(v_vs_571_);
v___x_577_ = lean_nat_dec_lt(v___x_575_, v___x_576_);
if (v___x_577_ == 0)
{
lean_object* v___x_579_; 
lean_dec_ref(v_vs_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 0);
lean_ctor_set(v___x_573_, 0, v_x_537_);
v___x_579_ = v___x_573_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_580_; 
v_reuseFailAlloc_580_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_580_, 0, v_x_537_);
v___x_579_ = v_reuseFailAlloc_580_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
return v___x_579_;
}
}
else
{
uint8_t v___x_581_; 
v___x_581_ = lean_nat_dec_le(v___x_576_, v___x_576_);
if (v___x_581_ == 0)
{
if (v___x_577_ == 0)
{
lean_object* v___x_583_; 
lean_dec_ref(v_vs_571_);
if (v_isShared_574_ == 0)
{
lean_ctor_set_tag(v___x_573_, 0);
lean_ctor_set(v___x_573_, 0, v_x_537_);
v___x_583_ = v___x_573_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_584_; 
v_reuseFailAlloc_584_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_584_, 0, v_x_537_);
v___x_583_ = v_reuseFailAlloc_584_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
return v___x_583_;
}
}
else
{
size_t v___x_585_; size_t v___x_586_; lean_object* v___x_587_; 
lean_del_object(v___x_573_);
v___x_585_ = ((size_t)0ULL);
v___x_586_ = lean_usize_of_nat(v___x_576_);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_571_, v___x_585_, v___x_586_, v_x_537_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec_ref(v_vs_571_);
return v___x_587_;
}
}
else
{
size_t v___x_588_; size_t v___x_589_; lean_object* v___x_590_; 
lean_del_object(v___x_573_);
v___x_588_ = ((size_t)0ULL);
v___x_589_ = lean_usize_of_nat(v___x_576_);
v___x_590_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_571_, v___x_588_, v___x_589_, v_x_537_, v___y_545_, v___y_546_, v___y_547_, v___y_548_);
lean_dec_ref(v_vs_571_);
return v___x_590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_592_, size_t v_i_593_, size_t v_stop_594_, lean_object* v_b_595_, lean_object* v___y_596_, lean_object* v___y_597_, lean_object* v___y_598_, lean_object* v___y_599_, lean_object* v___y_600_, lean_object* v___y_601_, lean_object* v___y_602_, lean_object* v___y_603_, lean_object* v___y_604_, lean_object* v___y_605_, lean_object* v___y_606_){
_start:
{
uint8_t v___x_608_; 
v___x_608_ = lean_usize_dec_eq(v_i_593_, v_stop_594_);
if (v___x_608_ == 0)
{
lean_object* v___x_609_; lean_object* v___x_610_; 
v___x_609_ = lean_array_uget_borrowed(v_as_592_, v_i_593_);
lean_inc(v___x_609_);
v___x_610_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_609_, v_b_595_, v___y_596_, v___y_597_, v___y_598_, v___y_599_, v___y_600_, v___y_601_, v___y_602_, v___y_603_, v___y_604_, v___y_605_, v___y_606_);
if (lean_obj_tag(v___x_610_) == 0)
{
lean_object* v_a_611_; size_t v___x_612_; size_t v___x_613_; 
v_a_611_ = lean_ctor_get(v___x_610_, 0);
lean_inc(v_a_611_);
lean_dec_ref_known(v___x_610_, 1);
v___x_612_ = ((size_t)1ULL);
v___x_613_ = lean_usize_add(v_i_593_, v___x_612_);
v_i_593_ = v___x_613_;
v_b_595_ = v_a_611_;
goto _start;
}
else
{
return v___x_610_;
}
}
else
{
lean_object* v___x_615_; 
v___x_615_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_615_, 0, v_b_595_);
return v___x_615_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_616_, lean_object* v_i_617_, lean_object* v_stop_618_, lean_object* v_b_619_, lean_object* v___y_620_, lean_object* v___y_621_, lean_object* v___y_622_, lean_object* v___y_623_, lean_object* v___y_624_, lean_object* v___y_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_){
_start:
{
size_t v_i_boxed_632_; size_t v_stop_boxed_633_; lean_object* v_res_634_; 
v_i_boxed_632_ = lean_unbox_usize(v_i_617_);
lean_dec(v_i_617_);
v_stop_boxed_633_ = lean_unbox_usize(v_stop_618_);
lean_dec(v_stop_618_);
v_res_634_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_616_, v_i_boxed_632_, v_stop_boxed_633_, v_b_619_, v___y_620_, v___y_621_, v___y_622_, v___y_623_, v___y_624_, v___y_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_);
lean_dec(v___y_630_);
lean_dec_ref(v___y_629_);
lean_dec(v___y_628_);
lean_dec_ref(v___y_627_);
lean_dec(v___y_626_);
lean_dec_ref(v___y_625_);
lean_dec(v___y_624_);
lean_dec_ref(v___y_623_);
lean_dec(v___y_622_);
lean_dec(v___y_621_);
lean_dec_ref(v___y_620_);
lean_dec_ref(v_as_616_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object* v_x_635_, lean_object* v_x_636_, lean_object* v___y_637_, lean_object* v___y_638_, lean_object* v___y_639_, lean_object* v___y_640_, lean_object* v___y_641_, lean_object* v___y_642_, lean_object* v___y_643_, lean_object* v___y_644_, lean_object* v___y_645_, lean_object* v___y_646_, lean_object* v___y_647_, lean_object* v___y_648_){
_start:
{
lean_object* v_res_649_; 
v_res_649_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_635_, v_x_636_, v___y_637_, v___y_638_, v___y_639_, v___y_640_, v___y_641_, v___y_642_, v___y_643_, v___y_644_, v___y_645_, v___y_646_, v___y_647_);
lean_dec(v___y_647_);
lean_dec_ref(v___y_646_);
lean_dec(v___y_645_);
lean_dec_ref(v___y_644_);
lean_dec(v___y_643_);
lean_dec_ref(v___y_642_);
lean_dec(v___y_641_);
lean_dec_ref(v___y_640_);
lean_dec(v___y_639_);
lean_dec(v___y_638_);
lean_dec_ref(v___y_637_);
return v_res_649_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_650_; 
v___x_650_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object* v_x_651_, size_t v_x_652_, size_t v_x_653_, lean_object* v_x_654_, lean_object* v___y_655_, lean_object* v___y_656_, lean_object* v___y_657_, lean_object* v___y_658_, lean_object* v___y_659_, lean_object* v___y_660_, lean_object* v___y_661_, lean_object* v___y_662_, lean_object* v___y_663_, lean_object* v___y_664_, lean_object* v___y_665_){
_start:
{
if (lean_obj_tag(v_x_651_) == 0)
{
lean_object* v_cs_667_; lean_object* v___x_668_; size_t v___x_669_; lean_object* v_j_670_; lean_object* v___x_671_; size_t v___x_672_; size_t v___x_673_; size_t v___x_674_; size_t v___x_675_; size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
v_cs_667_ = lean_ctor_get(v_x_651_, 0);
lean_inc_ref(v_cs_667_);
lean_dec_ref_known(v_x_651_, 1);
v___x_668_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
v___x_669_ = lean_usize_shift_right(v_x_652_, v_x_653_);
v_j_670_ = lean_usize_to_nat(v___x_669_);
v___x_671_ = lean_array_get_borrowed(v___x_668_, v_cs_667_, v_j_670_);
v___x_672_ = ((size_t)1ULL);
v___x_673_ = lean_usize_shift_left(v___x_672_, v_x_653_);
v___x_674_ = lean_usize_sub(v___x_673_, v___x_672_);
v___x_675_ = lean_usize_land(v_x_652_, v___x_674_);
v___x_676_ = ((size_t)5ULL);
v___x_677_ = lean_usize_sub(v_x_653_, v___x_676_);
lean_inc(v___x_671_);
v___x_678_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_671_, v___x_675_, v___x_677_, v_x_654_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
if (lean_obj_tag(v___x_678_) == 0)
{
lean_object* v_a_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; uint8_t v___x_683_; 
v_a_679_ = lean_ctor_get(v___x_678_, 0);
lean_inc(v_a_679_);
v___x_680_ = lean_unsigned_to_nat(1u);
v___x_681_ = lean_nat_add(v_j_670_, v___x_680_);
lean_dec(v_j_670_);
v___x_682_ = lean_array_get_size(v_cs_667_);
v___x_683_ = lean_nat_dec_lt(v___x_681_, v___x_682_);
if (v___x_683_ == 0)
{
lean_dec(v___x_681_);
lean_dec(v_a_679_);
lean_dec_ref(v_cs_667_);
return v___x_678_;
}
else
{
uint8_t v___x_684_; 
v___x_684_ = lean_nat_dec_le(v___x_682_, v___x_682_);
if (v___x_684_ == 0)
{
if (v___x_683_ == 0)
{
lean_dec(v___x_681_);
lean_dec(v_a_679_);
lean_dec_ref(v_cs_667_);
return v___x_678_;
}
else
{
size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
lean_dec_ref_known(v___x_678_, 1);
v___x_685_ = lean_usize_of_nat(v___x_681_);
lean_dec(v___x_681_);
v___x_686_ = lean_usize_of_nat(v___x_682_);
v___x_687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_667_, v___x_685_, v___x_686_, v_a_679_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec_ref(v_cs_667_);
return v___x_687_;
}
}
else
{
size_t v___x_688_; size_t v___x_689_; lean_object* v___x_690_; 
lean_dec_ref_known(v___x_678_, 1);
v___x_688_ = lean_usize_of_nat(v___x_681_);
lean_dec(v___x_681_);
v___x_689_ = lean_usize_of_nat(v___x_682_);
v___x_690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_667_, v___x_688_, v___x_689_, v_a_679_, v___y_655_, v___y_656_, v___y_657_, v___y_658_, v___y_659_, v___y_660_, v___y_661_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec_ref(v_cs_667_);
return v___x_690_;
}
}
}
else
{
lean_dec(v_j_670_);
lean_dec_ref(v_cs_667_);
return v___x_678_;
}
}
else
{
lean_object* v_vs_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_711_; 
v_vs_691_ = lean_ctor_get(v_x_651_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v_x_651_);
if (v_isSharedCheck_711_ == 0)
{
v___x_693_ = v_x_651_;
v_isShared_694_ = v_isSharedCheck_711_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_vs_691_);
lean_dec(v_x_651_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_711_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_696_; uint8_t v___x_697_; 
v___x_695_ = lean_usize_to_nat(v_x_652_);
v___x_696_ = lean_array_get_size(v_vs_691_);
v___x_697_ = lean_nat_dec_lt(v___x_695_, v___x_696_);
if (v___x_697_ == 0)
{
lean_object* v___x_699_; 
lean_dec(v___x_695_);
lean_dec_ref(v_vs_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 0);
lean_ctor_set(v___x_693_, 0, v_x_654_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_x_654_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
else
{
uint8_t v___x_701_; 
v___x_701_ = lean_nat_dec_le(v___x_696_, v___x_696_);
if (v___x_701_ == 0)
{
if (v___x_697_ == 0)
{
lean_object* v___x_703_; 
lean_dec(v___x_695_);
lean_dec_ref(v_vs_691_);
if (v_isShared_694_ == 0)
{
lean_ctor_set_tag(v___x_693_, 0);
lean_ctor_set(v___x_693_, 0, v_x_654_);
v___x_703_ = v___x_693_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v_x_654_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
else
{
size_t v___x_705_; size_t v___x_706_; lean_object* v___x_707_; 
lean_del_object(v___x_693_);
v___x_705_ = lean_usize_of_nat(v___x_695_);
lean_dec(v___x_695_);
v___x_706_ = lean_usize_of_nat(v___x_696_);
v___x_707_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_691_, v___x_705_, v___x_706_, v_x_654_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec_ref(v_vs_691_);
return v___x_707_;
}
}
else
{
size_t v___x_708_; size_t v___x_709_; lean_object* v___x_710_; 
lean_del_object(v___x_693_);
v___x_708_ = lean_usize_of_nat(v___x_695_);
lean_dec(v___x_695_);
v___x_709_ = lean_usize_of_nat(v___x_696_);
v___x_710_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_691_, v___x_708_, v___x_709_, v_x_654_, v___y_662_, v___y_663_, v___y_664_, v___y_665_);
lean_dec_ref(v_vs_691_);
return v___x_710_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_712_, lean_object* v_x_713_, lean_object* v_x_714_, lean_object* v_x_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_, lean_object* v___y_720_, lean_object* v___y_721_, lean_object* v___y_722_, lean_object* v___y_723_, lean_object* v___y_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_){
_start:
{
size_t v_x_24422__boxed_728_; size_t v_x_24423__boxed_729_; lean_object* v_res_730_; 
v_x_24422__boxed_728_ = lean_unbox_usize(v_x_713_);
lean_dec(v_x_713_);
v_x_24423__boxed_729_ = lean_unbox_usize(v_x_714_);
lean_dec(v_x_714_);
v_res_730_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_712_, v_x_24422__boxed_728_, v_x_24423__boxed_729_, v_x_715_, v___y_716_, v___y_717_, v___y_718_, v___y_719_, v___y_720_, v___y_721_, v___y_722_, v___y_723_, v___y_724_, v___y_725_, v___y_726_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
lean_dec(v___y_724_);
lean_dec_ref(v___y_723_);
lean_dec(v___y_722_);
lean_dec_ref(v___y_721_);
lean_dec(v___y_720_);
lean_dec_ref(v___y_719_);
lean_dec(v___y_718_);
lean_dec(v___y_717_);
lean_dec_ref(v___y_716_);
return v_res_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object* v_t_731_, lean_object* v_init_732_, lean_object* v_start_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_, lean_object* v___y_737_, lean_object* v___y_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; uint8_t v___x_747_; 
v___x_746_ = lean_unsigned_to_nat(0u);
v___x_747_ = lean_nat_dec_eq(v_start_733_, v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v_root_748_; lean_object* v_tail_749_; size_t v_shift_750_; lean_object* v_tailOff_751_; uint8_t v___x_752_; 
v_root_748_ = lean_ctor_get(v_t_731_, 0);
lean_inc_ref(v_root_748_);
v_tail_749_ = lean_ctor_get(v_t_731_, 1);
lean_inc_ref(v_tail_749_);
v_shift_750_ = lean_ctor_get_usize(v_t_731_, 4);
v_tailOff_751_ = lean_ctor_get(v_t_731_, 3);
lean_inc(v_tailOff_751_);
lean_dec_ref(v_t_731_);
v___x_752_ = lean_nat_dec_le(v_tailOff_751_, v_start_733_);
if (v___x_752_ == 0)
{
size_t v___x_753_; lean_object* v___x_754_; 
lean_dec(v_tailOff_751_);
v___x_753_ = lean_usize_of_nat(v_start_733_);
v___x_754_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_748_, v___x_753_, v_shift_750_, v_init_732_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_754_) == 0)
{
lean_object* v_a_755_; lean_object* v___x_756_; uint8_t v___x_757_; 
v_a_755_ = lean_ctor_get(v___x_754_, 0);
lean_inc(v_a_755_);
v___x_756_ = lean_array_get_size(v_tail_749_);
v___x_757_ = lean_nat_dec_lt(v___x_746_, v___x_756_);
if (v___x_757_ == 0)
{
lean_dec(v_a_755_);
lean_dec_ref(v_tail_749_);
return v___x_754_;
}
else
{
uint8_t v___x_758_; 
v___x_758_ = lean_nat_dec_le(v___x_756_, v___x_756_);
if (v___x_758_ == 0)
{
if (v___x_757_ == 0)
{
lean_dec(v_a_755_);
lean_dec_ref(v_tail_749_);
return v___x_754_;
}
else
{
size_t v___x_759_; size_t v___x_760_; lean_object* v___x_761_; 
lean_dec_ref_known(v___x_754_, 1);
v___x_759_ = ((size_t)0ULL);
v___x_760_ = lean_usize_of_nat(v___x_756_);
v___x_761_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_749_, v___x_759_, v___x_760_, v_a_755_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_tail_749_);
return v___x_761_;
}
}
else
{
size_t v___x_762_; size_t v___x_763_; lean_object* v___x_764_; 
lean_dec_ref_known(v___x_754_, 1);
v___x_762_ = ((size_t)0ULL);
v___x_763_ = lean_usize_of_nat(v___x_756_);
v___x_764_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_749_, v___x_762_, v___x_763_, v_a_755_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_tail_749_);
return v___x_764_;
}
}
}
else
{
lean_dec_ref(v_tail_749_);
return v___x_754_;
}
}
else
{
lean_object* v___x_765_; lean_object* v___x_766_; uint8_t v___x_767_; 
lean_dec_ref(v_root_748_);
v___x_765_ = lean_nat_sub(v_start_733_, v_tailOff_751_);
lean_dec(v_tailOff_751_);
v___x_766_ = lean_array_get_size(v_tail_749_);
v___x_767_ = lean_nat_dec_lt(v___x_765_, v___x_766_);
if (v___x_767_ == 0)
{
lean_object* v___x_768_; 
lean_dec(v___x_765_);
lean_dec_ref(v_tail_749_);
v___x_768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_768_, 0, v_init_732_);
return v___x_768_;
}
else
{
uint8_t v___x_769_; 
v___x_769_ = lean_nat_dec_le(v___x_766_, v___x_766_);
if (v___x_769_ == 0)
{
if (v___x_767_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v___x_765_);
lean_dec_ref(v_tail_749_);
v___x_770_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_770_, 0, v_init_732_);
return v___x_770_;
}
else
{
size_t v___x_771_; size_t v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_usize_of_nat(v___x_765_);
lean_dec(v___x_765_);
v___x_772_ = lean_usize_of_nat(v___x_766_);
v___x_773_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_749_, v___x_771_, v___x_772_, v_init_732_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_tail_749_);
return v___x_773_;
}
}
else
{
size_t v___x_774_; size_t v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_usize_of_nat(v___x_765_);
lean_dec(v___x_765_);
v___x_775_ = lean_usize_of_nat(v___x_766_);
v___x_776_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_749_, v___x_774_, v___x_775_, v_init_732_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_tail_749_);
return v___x_776_;
}
}
}
}
else
{
lean_object* v_root_777_; lean_object* v_tail_778_; lean_object* v___x_779_; 
v_root_777_ = lean_ctor_get(v_t_731_, 0);
lean_inc_ref(v_root_777_);
v_tail_778_ = lean_ctor_get(v_t_731_, 1);
lean_inc_ref(v_tail_778_);
lean_dec_ref(v_t_731_);
v___x_779_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_777_, v_init_732_, v___y_734_, v___y_735_, v___y_736_, v___y_737_, v___y_738_, v___y_739_, v___y_740_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
if (lean_obj_tag(v___x_779_) == 0)
{
lean_object* v_a_780_; lean_object* v___x_781_; uint8_t v___x_782_; 
v_a_780_ = lean_ctor_get(v___x_779_, 0);
lean_inc(v_a_780_);
v___x_781_ = lean_array_get_size(v_tail_778_);
v___x_782_ = lean_nat_dec_lt(v___x_746_, v___x_781_);
if (v___x_782_ == 0)
{
lean_dec(v_a_780_);
lean_dec_ref(v_tail_778_);
return v___x_779_;
}
else
{
uint8_t v___x_783_; 
v___x_783_ = lean_nat_dec_le(v___x_781_, v___x_781_);
if (v___x_783_ == 0)
{
if (v___x_782_ == 0)
{
lean_dec(v_a_780_);
lean_dec_ref(v_tail_778_);
return v___x_779_;
}
else
{
size_t v___x_784_; size_t v___x_785_; lean_object* v___x_786_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_784_ = ((size_t)0ULL);
v___x_785_ = lean_usize_of_nat(v___x_781_);
v___x_786_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_778_, v___x_784_, v___x_785_, v_a_780_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_tail_778_);
return v___x_786_;
}
}
else
{
size_t v___x_787_; size_t v___x_788_; lean_object* v___x_789_; 
lean_dec_ref_known(v___x_779_, 1);
v___x_787_ = ((size_t)0ULL);
v___x_788_ = lean_usize_of_nat(v___x_781_);
v___x_789_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_778_, v___x_787_, v___x_788_, v_a_780_, v___y_741_, v___y_742_, v___y_743_, v___y_744_);
lean_dec_ref(v_tail_778_);
return v___x_789_;
}
}
}
else
{
lean_dec_ref(v_tail_778_);
return v___x_779_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object* v_t_790_, lean_object* v_init_791_, lean_object* v_start_792_, lean_object* v___y_793_, lean_object* v___y_794_, lean_object* v___y_795_, lean_object* v___y_796_, lean_object* v___y_797_, lean_object* v___y_798_, lean_object* v___y_799_, lean_object* v___y_800_, lean_object* v___y_801_, lean_object* v___y_802_, lean_object* v___y_803_, lean_object* v___y_804_){
_start:
{
lean_object* v_res_805_; 
v_res_805_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_790_, v_init_791_, v_start_792_, v___y_793_, v___y_794_, v___y_795_, v___y_796_, v___y_797_, v___y_798_, v___y_799_, v___y_800_, v___y_801_, v___y_802_, v___y_803_);
lean_dec(v___y_803_);
lean_dec_ref(v___y_802_);
lean_dec(v___y_801_);
lean_dec_ref(v___y_800_);
lean_dec(v___y_799_);
lean_dec_ref(v___y_798_);
lean_dec(v___y_797_);
lean_dec_ref(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v___y_794_);
lean_dec_ref(v___y_793_);
lean_dec(v_start_792_);
return v_res_805_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(lean_object* v_lctx_806_, lean_object* v_init_807_, lean_object* v_start_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_, lean_object* v___y_816_, lean_object* v___y_817_, lean_object* v___y_818_, lean_object* v___y_819_){
_start:
{
lean_object* v_decls_821_; lean_object* v___x_822_; 
v_decls_821_ = lean_ctor_get(v_lctx_806_, 1);
lean_inc_ref(v_decls_821_);
lean_dec_ref(v_lctx_806_);
v___x_822_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_821_, v_init_807_, v_start_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_, v___y_815_, v___y_816_, v___y_817_, v___y_818_, v___y_819_);
return v___x_822_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object* v_lctx_823_, lean_object* v_init_824_, lean_object* v_start_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_, lean_object* v___y_835_, lean_object* v___y_836_, lean_object* v___y_837_){
_start:
{
lean_object* v_res_838_; 
v_res_838_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_823_, v_init_824_, v_start_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_, v___y_834_, v___y_835_, v___y_836_);
lean_dec(v___y_836_);
lean_dec_ref(v___y_835_);
lean_dec(v___y_834_);
lean_dec_ref(v___y_833_);
lean_dec(v___y_832_);
lean_dec_ref(v___y_831_);
lean_dec(v___y_830_);
lean_dec_ref(v___y_829_);
lean_dec(v___y_828_);
lean_dec(v___y_827_);
lean_dec_ref(v___y_826_);
lean_dec(v_start_825_);
return v_res_838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(lean_object* v_scope_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_, lean_object* v___y_843_, lean_object* v___y_844_, lean_object* v___y_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_lctx_852_; lean_object* v_decls_853_; lean_object* v_nextDeclIdx_854_; lean_object* v_size_855_; uint8_t v___x_856_; 
v_lctx_852_ = lean_ctor_get(v___y_847_, 2);
v_decls_853_ = lean_ctor_get(v_lctx_852_, 1);
v_nextDeclIdx_854_ = lean_ctor_get(v_scope_839_, 3);
v_size_855_ = lean_ctor_get(v_decls_853_, 2);
v___x_856_ = lean_nat_dec_eq(v_nextDeclIdx_854_, v_size_855_);
if (v___x_856_ == 0)
{
lean_object* v___x_857_; 
lean_inc(v_nextDeclIdx_854_);
lean_inc_ref(v_lctx_852_);
v___x_857_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_852_, v_scope_839_, v_nextDeclIdx_854_, v___y_840_, v___y_841_, v___y_842_, v___y_843_, v___y_844_, v___y_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_, v___y_850_);
lean_dec(v_nextDeclIdx_854_);
if (lean_obj_tag(v___x_857_) == 0)
{
lean_object* v_a_858_; lean_object* v___x_860_; uint8_t v_isShared_861_; uint8_t v_isSharedCheck_876_; 
v_a_858_ = lean_ctor_get(v___x_857_, 0);
v_isSharedCheck_876_ = !lean_is_exclusive(v___x_857_);
if (v_isSharedCheck_876_ == 0)
{
v___x_860_ = v___x_857_;
v_isShared_861_ = v_isSharedCheck_876_;
goto v_resetjp_859_;
}
else
{
lean_inc(v_a_858_);
lean_dec(v___x_857_);
v___x_860_ = lean_box(0);
v_isShared_861_ = v_isSharedCheck_876_;
goto v_resetjp_859_;
}
v_resetjp_859_:
{
lean_object* v_specs_862_; lean_object* v_jps_863_; lean_object* v_lastLiftedPre_x3f_864_; lean_object* v___x_866_; uint8_t v_isShared_867_; uint8_t v_isSharedCheck_874_; 
v_specs_862_ = lean_ctor_get(v_a_858_, 0);
v_jps_863_ = lean_ctor_get(v_a_858_, 1);
v_lastLiftedPre_x3f_864_ = lean_ctor_get(v_a_858_, 2);
v_isSharedCheck_874_ = !lean_is_exclusive(v_a_858_);
if (v_isSharedCheck_874_ == 0)
{
lean_object* v_unused_875_; 
v_unused_875_ = lean_ctor_get(v_a_858_, 3);
lean_dec(v_unused_875_);
v___x_866_ = v_a_858_;
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
else
{
lean_inc(v_lastLiftedPre_x3f_864_);
lean_inc(v_jps_863_);
lean_inc(v_specs_862_);
lean_dec(v_a_858_);
v___x_866_ = lean_box(0);
v_isShared_867_ = v_isSharedCheck_874_;
goto v_resetjp_865_;
}
v_resetjp_865_:
{
lean_object* v___x_869_; 
lean_inc(v_size_855_);
if (v_isShared_867_ == 0)
{
lean_ctor_set(v___x_866_, 3, v_size_855_);
v___x_869_ = v___x_866_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_specs_862_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v_jps_863_);
lean_ctor_set(v_reuseFailAlloc_873_, 2, v_lastLiftedPre_x3f_864_);
lean_ctor_set(v_reuseFailAlloc_873_, 3, v_size_855_);
v___x_869_ = v_reuseFailAlloc_873_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_871_; 
if (v_isShared_861_ == 0)
{
lean_ctor_set(v___x_860_, 0, v___x_869_);
v___x_871_ = v___x_860_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v___x_869_);
v___x_871_ = v_reuseFailAlloc_872_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
return v___x_871_;
}
}
}
}
}
else
{
return v___x_857_;
}
}
else
{
lean_object* v___x_877_; 
v___x_877_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_877_, 0, v_scope_839_);
return v___x_877_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object* v_scope_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_){
_start:
{
lean_object* v_res_891_; 
v_res_891_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(v_scope_878_, v___y_879_, v___y_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec_ref(v___y_882_);
lean_dec(v___y_881_);
lean_dec(v___y_880_);
lean_dec_ref(v___y_879_);
return v_res_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(lean_object* v_scope_892_, lean_object* v_goal_893_, lean_object* v_a_894_, lean_object* v_a_895_, lean_object* v_a_896_, lean_object* v_a_897_, lean_object* v_a_898_, lean_object* v_a_899_, lean_object* v_a_900_, lean_object* v_a_901_, lean_object* v_a_902_, lean_object* v_a_903_, lean_object* v_a_904_){
_start:
{
lean_object* v___f_906_; lean_object* v___x_907_; 
v___f_906_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_906_, 0, v_scope_892_);
v___x_907_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_893_, v___f_906_, v_a_894_, v_a_895_, v_a_896_, v_a_897_, v_a_898_, v_a_899_, v_a_900_, v_a_901_, v_a_902_, v_a_903_, v_a_904_);
return v___x_907_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___boxed(lean_object* v_scope_908_, lean_object* v_goal_909_, lean_object* v_a_910_, lean_object* v_a_911_, lean_object* v_a_912_, lean_object* v_a_913_, lean_object* v_a_914_, lean_object* v_a_915_, lean_object* v_a_916_, lean_object* v_a_917_, lean_object* v_a_918_, lean_object* v_a_919_, lean_object* v_a_920_, lean_object* v_a_921_){
_start:
{
lean_object* v_res_922_; 
v_res_922_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_908_, v_goal_909_, v_a_910_, v_a_911_, v_a_912_, v_a_913_, v_a_914_, v_a_915_, v_a_916_, v_a_917_, v_a_918_, v_a_919_, v_a_920_);
lean_dec(v_a_920_);
lean_dec_ref(v_a_919_);
lean_dec(v_a_918_);
lean_dec_ref(v_a_917_);
lean_dec(v_a_916_);
lean_dec_ref(v_a_915_);
lean_dec(v_a_914_);
lean_dec_ref(v_a_913_);
lean_dec(v_a_912_);
lean_dec(v_a_911_);
lean_dec_ref(v_a_910_);
return v_res_922_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object* v_as_923_, size_t v_i_924_, size_t v_stop_925_, lean_object* v_b_926_, lean_object* v___y_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_){
_start:
{
lean_object* v___x_939_; 
v___x_939_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_923_, v_i_924_, v_stop_925_, v_b_926_, v___y_934_, v___y_935_, v___y_936_, v___y_937_);
return v___x_939_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object* v_as_940_, lean_object* v_i_941_, lean_object* v_stop_942_, lean_object* v_b_943_, lean_object* v___y_944_, lean_object* v___y_945_, lean_object* v___y_946_, lean_object* v___y_947_, lean_object* v___y_948_, lean_object* v___y_949_, lean_object* v___y_950_, lean_object* v___y_951_, lean_object* v___y_952_, lean_object* v___y_953_, lean_object* v___y_954_, lean_object* v___y_955_){
_start:
{
size_t v_i_boxed_956_; size_t v_stop_boxed_957_; lean_object* v_res_958_; 
v_i_boxed_956_ = lean_unbox_usize(v_i_941_);
lean_dec(v_i_941_);
v_stop_boxed_957_ = lean_unbox_usize(v_stop_942_);
lean_dec(v_stop_942_);
v_res_958_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_940_, v_i_boxed_956_, v_stop_boxed_957_, v_b_943_, v___y_944_, v___y_945_, v___y_946_, v___y_947_, v___y_948_, v___y_949_, v___y_950_, v___y_951_, v___y_952_, v___y_953_, v___y_954_);
lean_dec(v___y_954_);
lean_dec_ref(v___y_953_);
lean_dec(v___y_952_);
lean_dec_ref(v___y_951_);
lean_dec(v___y_950_);
lean_dec_ref(v___y_949_);
lean_dec(v___y_948_);
lean_dec_ref(v___y_947_);
lean_dec(v___y_946_);
lean_dec(v___y_945_);
lean_dec_ref(v___y_944_);
lean_dec_ref(v_as_940_);
return v_res_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object* v_a_959_){
_start:
{
lean_object* v___x_961_; lean_object* v_fuel_962_; 
v___x_961_ = lean_st_ref_get(v_a_959_);
v_fuel_962_ = lean_ctor_get(v___x_961_, 7);
lean_inc(v_fuel_962_);
lean_dec(v___x_961_);
if (lean_obj_tag(v_fuel_962_) == 0)
{
lean_object* v_n_963_; lean_object* v___x_965_; uint8_t v_isShared_966_; uint8_t v_isSharedCheck_973_; 
v_n_963_ = lean_ctor_get(v_fuel_962_, 0);
v_isSharedCheck_973_ = !lean_is_exclusive(v_fuel_962_);
if (v_isSharedCheck_973_ == 0)
{
v___x_965_ = v_fuel_962_;
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
else
{
lean_inc(v_n_963_);
lean_dec(v_fuel_962_);
v___x_965_ = lean_box(0);
v_isShared_966_ = v_isSharedCheck_973_;
goto v_resetjp_964_;
}
v_resetjp_964_:
{
lean_object* v___x_967_; uint8_t v___x_968_; lean_object* v___x_969_; lean_object* v___x_971_; 
v___x_967_ = lean_unsigned_to_nat(0u);
v___x_968_ = lean_nat_dec_eq(v_n_963_, v___x_967_);
lean_dec(v_n_963_);
v___x_969_ = lean_box(v___x_968_);
if (v_isShared_966_ == 0)
{
lean_ctor_set(v___x_965_, 0, v___x_969_);
v___x_971_ = v___x_965_;
goto v_reusejp_970_;
}
else
{
lean_object* v_reuseFailAlloc_972_; 
v_reuseFailAlloc_972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_972_, 0, v___x_969_);
v___x_971_ = v_reuseFailAlloc_972_;
goto v_reusejp_970_;
}
v_reusejp_970_:
{
return v___x_971_;
}
}
}
else
{
uint8_t v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; 
lean_dec(v_fuel_962_);
v___x_974_ = 0;
v___x_975_ = lean_box(v___x_974_);
v___x_976_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_976_, 0, v___x_975_);
return v___x_976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg___boxed(lean_object* v_a_977_, lean_object* v_a_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_977_);
lean_dec(v_a_977_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(lean_object* v_a_980_, lean_object* v_a_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_){
_start:
{
lean_object* v___x_992_; 
v___x_992_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_981_);
return v___x_992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___boxed(lean_object* v_a_993_, lean_object* v_a_994_, lean_object* v_a_995_, lean_object* v_a_996_, lean_object* v_a_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_){
_start:
{
lean_object* v_res_1005_; 
v_res_1005_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(v_a_993_, v_a_994_, v_a_995_, v_a_996_, v_a_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_);
lean_dec(v_a_1003_);
lean_dec_ref(v_a_1002_);
lean_dec(v_a_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_a_997_);
lean_dec_ref(v_a_996_);
lean_dec(v_a_995_);
lean_dec(v_a_994_);
lean_dec_ref(v_a_993_);
return v_res_1005_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object* v_a_1006_){
_start:
{
lean_object* v___x_1008_; lean_object* v_specBackwardRuleCache_1009_; lean_object* v_splitBackwardRuleCache_1010_; lean_object* v_latticeBackwardRuleCache_1011_; lean_object* v_frameDB_x3f_1012_; lean_object* v_invariants_1013_; lean_object* v_vcs_1014_; lean_object* v_simpState_1015_; lean_object* v_fuel_1016_; lean_object* v_inlineHandledInvariants_1017_; lean_object* v___x_1019_; uint8_t v_isShared_1020_; uint8_t v_isSharedCheck_1042_; 
v___x_1008_ = lean_st_ref_take(v_a_1006_);
v_specBackwardRuleCache_1009_ = lean_ctor_get(v___x_1008_, 0);
v_splitBackwardRuleCache_1010_ = lean_ctor_get(v___x_1008_, 1);
v_latticeBackwardRuleCache_1011_ = lean_ctor_get(v___x_1008_, 2);
v_frameDB_x3f_1012_ = lean_ctor_get(v___x_1008_, 3);
v_invariants_1013_ = lean_ctor_get(v___x_1008_, 4);
v_vcs_1014_ = lean_ctor_get(v___x_1008_, 5);
v_simpState_1015_ = lean_ctor_get(v___x_1008_, 6);
v_fuel_1016_ = lean_ctor_get(v___x_1008_, 7);
v_inlineHandledInvariants_1017_ = lean_ctor_get(v___x_1008_, 8);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1019_ = v___x_1008_;
v_isShared_1020_ = v_isSharedCheck_1042_;
goto v_resetjp_1018_;
}
else
{
lean_inc(v_inlineHandledInvariants_1017_);
lean_inc(v_fuel_1016_);
lean_inc(v_simpState_1015_);
lean_inc(v_vcs_1014_);
lean_inc(v_invariants_1013_);
lean_inc(v_frameDB_x3f_1012_);
lean_inc(v_latticeBackwardRuleCache_1011_);
lean_inc(v_splitBackwardRuleCache_1010_);
lean_inc(v_specBackwardRuleCache_1009_);
lean_dec(v___x_1008_);
v___x_1019_ = lean_box(0);
v_isShared_1020_ = v_isSharedCheck_1042_;
goto v_resetjp_1018_;
}
v_resetjp_1018_:
{
lean_object* v___x_1021_; lean_object* v___y_1023_; 
v___x_1021_ = lean_box(0);
if (lean_obj_tag(v_fuel_1016_) == 0)
{
lean_object* v_n_1029_; lean_object* v_zero_1030_; uint8_t v_isZero_1031_; 
v_n_1029_ = lean_ctor_get(v_fuel_1016_, 0);
v_zero_1030_ = lean_unsigned_to_nat(0u);
v_isZero_1031_ = lean_nat_dec_eq(v_n_1029_, v_zero_1030_);
if (v_isZero_1031_ == 0)
{
lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1040_; 
lean_inc(v_n_1029_);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_fuel_1016_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_fuel_1016_, 0);
lean_dec(v_unused_1041_);
v___x_1033_ = v_fuel_1016_;
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
else
{
lean_dec(v_fuel_1016_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1040_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v_one_1035_; lean_object* v_n_1036_; lean_object* v___x_1038_; 
v_one_1035_ = lean_unsigned_to_nat(1u);
v_n_1036_ = lean_nat_sub(v_n_1029_, v_one_1035_);
lean_dec(v_n_1029_);
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v_n_1036_);
v___x_1038_ = v___x_1033_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v_n_1036_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
v___y_1023_ = v___x_1038_;
goto v___jp_1022_;
}
}
}
else
{
v___y_1023_ = v_fuel_1016_;
goto v___jp_1022_;
}
}
else
{
v___y_1023_ = v_fuel_1016_;
goto v___jp_1022_;
}
v___jp_1022_:
{
lean_object* v___x_1025_; 
if (v_isShared_1020_ == 0)
{
lean_ctor_set(v___x_1019_, 7, v___y_1023_);
v___x_1025_ = v___x_1019_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_specBackwardRuleCache_1009_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_splitBackwardRuleCache_1010_);
lean_ctor_set(v_reuseFailAlloc_1028_, 2, v_latticeBackwardRuleCache_1011_);
lean_ctor_set(v_reuseFailAlloc_1028_, 3, v_frameDB_x3f_1012_);
lean_ctor_set(v_reuseFailAlloc_1028_, 4, v_invariants_1013_);
lean_ctor_set(v_reuseFailAlloc_1028_, 5, v_vcs_1014_);
lean_ctor_set(v_reuseFailAlloc_1028_, 6, v_simpState_1015_);
lean_ctor_set(v_reuseFailAlloc_1028_, 7, v___y_1023_);
lean_ctor_set(v_reuseFailAlloc_1028_, 8, v_inlineHandledInvariants_1017_);
v___x_1025_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; 
v___x_1026_ = lean_st_ref_set(v_a_1006_, v___x_1025_);
v___x_1027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1027_, 0, v___x_1021_);
return v___x_1027_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg___boxed(lean_object* v_a_1043_, lean_object* v_a_1044_){
_start:
{
lean_object* v_res_1045_; 
v_res_1045_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_1043_);
lean_dec(v_a_1043_);
return v_res_1045_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(lean_object* v_a_1046_, lean_object* v_a_1047_, lean_object* v_a_1048_, lean_object* v_a_1049_, lean_object* v_a_1050_, lean_object* v_a_1051_, lean_object* v_a_1052_, lean_object* v_a_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_, lean_object* v_a_1056_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_1047_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___boxed(lean_object* v_a_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_, lean_object* v_a_1062_, lean_object* v_a_1063_, lean_object* v_a_1064_, lean_object* v_a_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_){
_start:
{
lean_object* v_res_1071_; 
v_res_1071_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(v_a_1059_, v_a_1060_, v_a_1061_, v_a_1062_, v_a_1063_, v_a_1064_, v_a_1065_, v_a_1066_, v_a_1067_, v_a_1068_, v_a_1069_);
lean_dec(v_a_1069_);
lean_dec_ref(v_a_1068_);
lean_dec(v_a_1067_);
lean_dec_ref(v_a_1066_);
lean_dec(v_a_1065_);
lean_dec_ref(v_a_1064_);
lean_dec(v_a_1063_);
lean_dec_ref(v_a_1062_);
lean_dec(v_a_1061_);
lean_dec(v_a_1060_);
lean_dec_ref(v_a_1059_);
return v_res_1071_;
}
}
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_VCGen_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Tactic_Do_Internal_VCGen_SpecDB(uint8_t builtin);
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
