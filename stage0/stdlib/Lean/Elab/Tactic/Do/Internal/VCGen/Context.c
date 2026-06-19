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
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
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
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_st_ref_take(lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Sym_mkBackwardRuleFromDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_deferred_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_deferred_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_elaborated_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_elaborated_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__1_value;
static const lean_array_object l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__2 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__0 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__0_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__1 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__1_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "vcgen"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 84, 199, 228, 250, 36, 60, 178)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__1_value),LEAN_SCALAR_PTR_LITERAL(180, 190, 140, 210, 253, 78, 130, 238)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__2_value),LEAN_SCALAR_PTR_LITERAL(212, 104, 229, 54, 179, 197, 12, 87)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__3_value),LEAN_SCALAR_PTR_LITERAL(49, 235, 69, 93, 100, 93, 190, 221)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__5_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__7;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "`until` pattern elaborated to "};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__9;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m___boxed(lean_object*);
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
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Triple"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__2_value),LEAN_SCALAR_PTR_LITERAL(190, 57, 218, 157, 42, 52, 8, 129)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(33, 54, 193, 255, 75, 233, 191, 151)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Order"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "le_of_forall_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__7_value),LEAN_SCALAR_PTR_LITERAL(101, 62, 242, 60, 214, 49, 44, 186)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "le_of_imp_top_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__9_value),LEAN_SCALAR_PTR_LITERAL(93, 90, 131, 207, 158, 255, 244, 86)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "ofProp_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__11_value),LEAN_SCALAR_PTR_LITERAL(170, 72, 238, 67, 89, 176, 13, 2)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "true_le_of_top_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__13_value),LEAN_SCALAR_PTR_LITERAL(246, 158, 62, 101, 253, 23, 66, 126)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "top_le_prop"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__15_value),LEAN_SCALAR_PTR_LITERAL(100, 220, 104, 174, 27, 127, 1, 211)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__17_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__3_value),LEAN_SCALAR_PTR_LITERAL(58, 46, 244, 208, 18, 71, 77, 162)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PartialOrder"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rel_refl"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__20 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__5_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__6_value),LEAN_SCALAR_PTR_LITERAL(47, 93, 74, 241, 117, 210, 202, 6)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__19_value),LEAN_SCALAR_PTR_LITERAL(179, 3, 218, 237, 219, 72, 94, 177)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__20_value),LEAN_SCALAR_PTR_LITERAL(114, 93, 162, 136, 122, 175, 235, 220)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "CompleteLattice"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value;
static const lean_string_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "meet_top_le_of_le"};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__23 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__23_value;
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value_aux_0),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__1_value),LEAN_SCALAR_PTR_LITERAL(225, 148, 172, 135, 227, 248, 47, 24)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value_aux_1),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 204, 33, 109, 120, 201, 43, 17)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value_aux_2),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__22_value),LEAN_SCALAR_PTR_LITERAL(237, 11, 99, 181, 146, 193, 255, 229)}};
static const lean_ctor_object l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value_aux_3),((lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__23_value),LEAN_SCALAR_PTR_LITERAL(136, 104, 44, 170, 221, 184, 131, 100)}};
static const lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24 = (const lean_object*)&l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24_value;
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorIdx(lean_object* v_x_1_){
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorIdx___boxed(lean_object* v_x_4_){
_start:
{
lean_object* v_res_5_; 
v_res_5_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorIdx(v_x_4_);
lean_dec_ref(v_x_4_);
return v_res_5_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___redArg(lean_object* v_t_6_, lean_object* v_k_7_){
_start:
{
lean_object* v_elabFn_8_; lean_object* v___x_9_; 
v_elabFn_8_ = lean_ctor_get(v_t_6_, 0);
lean_inc_ref(v_elabFn_8_);
lean_dec_ref(v_t_6_);
v___x_9_ = lean_apply_1(v_k_7_, v_elabFn_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim(lean_object* v_motive_10_, lean_object* v_ctorIdx_11_, lean_object* v_t_12_, lean_object* v_h_13_, lean_object* v_k_14_){
_start:
{
lean_object* v___x_15_; 
v___x_15_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___redArg(v_t_12_, v_k_14_);
return v___x_15_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___boxed(lean_object* v_motive_16_, lean_object* v_ctorIdx_17_, lean_object* v_t_18_, lean_object* v_h_19_, lean_object* v_k_20_){
_start:
{
lean_object* v_res_21_; 
v_res_21_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim(v_motive_16_, v_ctorIdx_17_, v_t_18_, v_h_19_, v_k_20_);
lean_dec(v_ctorIdx_17_);
return v_res_21_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_deferred_elim___redArg(lean_object* v_t_22_, lean_object* v_deferred_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___redArg(v_t_22_, v_deferred_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_deferred_elim(lean_object* v_motive_25_, lean_object* v_t_26_, lean_object* v_h_27_, lean_object* v_deferred_28_){
_start:
{
lean_object* v___x_29_; 
v___x_29_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___redArg(v_t_26_, v_deferred_28_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_elaborated_elim___redArg(lean_object* v_t_30_, lean_object* v_elaborated_31_){
_start:
{
lean_object* v___x_32_; 
v___x_32_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___redArg(v_t_30_, v_elaborated_31_);
return v___x_32_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_elaborated_elim(lean_object* v_motive_33_, lean_object* v_t_34_, lean_object* v_h_35_, lean_object* v_elaborated_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_ctorElim___redArg(v_t_34_, v_elaborated_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0_spec__0(lean_object* v_msgData_38_, lean_object* v___y_39_, lean_object* v___y_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v___x_44_; lean_object* v_env_45_; lean_object* v___x_46_; lean_object* v_mctx_47_; lean_object* v_lctx_48_; lean_object* v_options_49_; lean_object* v___x_50_; lean_object* v___x_51_; lean_object* v___x_52_; 
v___x_44_ = lean_st_ref_get(v___y_42_);
v_env_45_ = lean_ctor_get(v___x_44_, 0);
lean_inc_ref(v_env_45_);
lean_dec(v___x_44_);
v___x_46_ = lean_st_ref_get(v___y_40_);
v_mctx_47_ = lean_ctor_get(v___x_46_, 0);
lean_inc_ref(v_mctx_47_);
lean_dec(v___x_46_);
v_lctx_48_ = lean_ctor_get(v___y_39_, 2);
v_options_49_ = lean_ctor_get(v___y_41_, 2);
lean_inc_ref(v_options_49_);
lean_inc_ref(v_lctx_48_);
v___x_50_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_50_, 0, v_env_45_);
lean_ctor_set(v___x_50_, 1, v_mctx_47_);
lean_ctor_set(v___x_50_, 2, v_lctx_48_);
lean_ctor_set(v___x_50_, 3, v_options_49_);
v___x_51_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_51_, 0, v___x_50_);
lean_ctor_set(v___x_51_, 1, v_msgData_38_);
v___x_52_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_52_, 0, v___x_51_);
return v___x_52_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0_spec__0___boxed(lean_object* v_msgData_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0_spec__0(v_msgData_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_59_;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__0(void){
_start:
{
lean_object* v___x_60_; double v___x_61_; 
v___x_60_ = lean_unsigned_to_nat(0u);
v___x_61_ = lean_float_of_nat(v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0(lean_object* v_cls_65_, lean_object* v_msg_66_, lean_object* v___y_67_, lean_object* v___y_68_, lean_object* v___y_69_, lean_object* v___y_70_){
_start:
{
lean_object* v_ref_72_; lean_object* v___x_73_; lean_object* v_a_74_; lean_object* v___x_76_; uint8_t v_isShared_77_; uint8_t v_isSharedCheck_118_; 
v_ref_72_ = lean_ctor_get(v___y_69_, 5);
v___x_73_ = l_Lean_addMessageContextFull___at___00Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0_spec__0(v_msg_66_, v___y_67_, v___y_68_, v___y_69_, v___y_70_);
v_a_74_ = lean_ctor_get(v___x_73_, 0);
v_isSharedCheck_118_ = !lean_is_exclusive(v___x_73_);
if (v_isSharedCheck_118_ == 0)
{
v___x_76_ = v___x_73_;
v_isShared_77_ = v_isSharedCheck_118_;
goto v_resetjp_75_;
}
else
{
lean_inc(v_a_74_);
lean_dec(v___x_73_);
v___x_76_ = lean_box(0);
v_isShared_77_ = v_isSharedCheck_118_;
goto v_resetjp_75_;
}
v_resetjp_75_:
{
lean_object* v___x_78_; lean_object* v_traceState_79_; lean_object* v_env_80_; lean_object* v_nextMacroScope_81_; lean_object* v_ngen_82_; lean_object* v_auxDeclNGen_83_; lean_object* v_cache_84_; lean_object* v_messages_85_; lean_object* v_infoState_86_; lean_object* v_snapshotTasks_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_117_; 
v___x_78_ = lean_st_ref_take(v___y_70_);
v_traceState_79_ = lean_ctor_get(v___x_78_, 4);
v_env_80_ = lean_ctor_get(v___x_78_, 0);
v_nextMacroScope_81_ = lean_ctor_get(v___x_78_, 1);
v_ngen_82_ = lean_ctor_get(v___x_78_, 2);
v_auxDeclNGen_83_ = lean_ctor_get(v___x_78_, 3);
v_cache_84_ = lean_ctor_get(v___x_78_, 5);
v_messages_85_ = lean_ctor_get(v___x_78_, 6);
v_infoState_86_ = lean_ctor_get(v___x_78_, 7);
v_snapshotTasks_87_ = lean_ctor_get(v___x_78_, 8);
v_isSharedCheck_117_ = !lean_is_exclusive(v___x_78_);
if (v_isSharedCheck_117_ == 0)
{
v___x_89_ = v___x_78_;
v_isShared_90_ = v_isSharedCheck_117_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_snapshotTasks_87_);
lean_inc(v_infoState_86_);
lean_inc(v_messages_85_);
lean_inc(v_cache_84_);
lean_inc(v_traceState_79_);
lean_inc(v_auxDeclNGen_83_);
lean_inc(v_ngen_82_);
lean_inc(v_nextMacroScope_81_);
lean_inc(v_env_80_);
lean_dec(v___x_78_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_117_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint64_t v_tid_91_; lean_object* v_traces_92_; lean_object* v___x_94_; uint8_t v_isShared_95_; uint8_t v_isSharedCheck_116_; 
v_tid_91_ = lean_ctor_get_uint64(v_traceState_79_, sizeof(void*)*1);
v_traces_92_ = lean_ctor_get(v_traceState_79_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_traceState_79_);
if (v_isSharedCheck_116_ == 0)
{
v___x_94_ = v_traceState_79_;
v_isShared_95_ = v_isSharedCheck_116_;
goto v_resetjp_93_;
}
else
{
lean_inc(v_traces_92_);
lean_dec(v_traceState_79_);
v___x_94_ = lean_box(0);
v_isShared_95_ = v_isSharedCheck_116_;
goto v_resetjp_93_;
}
v_resetjp_93_:
{
lean_object* v___x_96_; double v___x_97_; uint8_t v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_96_ = lean_box(0);
v___x_97_ = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__0, &l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__0);
v___x_98_ = 0;
v___x_99_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__1));
v___x_100_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_100_, 0, v_cls_65_);
lean_ctor_set(v___x_100_, 1, v___x_96_);
lean_ctor_set(v___x_100_, 2, v___x_99_);
lean_ctor_set_float(v___x_100_, sizeof(void*)*3, v___x_97_);
lean_ctor_set_float(v___x_100_, sizeof(void*)*3 + 8, v___x_97_);
lean_ctor_set_uint8(v___x_100_, sizeof(void*)*3 + 16, v___x_98_);
v___x_101_ = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___closed__2));
v___x_102_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_100_);
lean_ctor_set(v___x_102_, 1, v_a_74_);
lean_ctor_set(v___x_102_, 2, v___x_101_);
lean_inc(v_ref_72_);
v___x_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_103_, 0, v_ref_72_);
lean_ctor_set(v___x_103_, 1, v___x_102_);
v___x_104_ = l_Lean_PersistentArray_push___redArg(v_traces_92_, v___x_103_);
if (v_isShared_95_ == 0)
{
lean_ctor_set(v___x_94_, 0, v___x_104_);
v___x_106_ = v___x_94_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_104_);
lean_ctor_set_uint64(v_reuseFailAlloc_115_, sizeof(void*)*1, v_tid_91_);
v___x_106_ = v_reuseFailAlloc_115_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
lean_object* v___x_108_; 
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 4, v___x_106_);
v___x_108_ = v___x_89_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_114_; 
v_reuseFailAlloc_114_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_114_, 0, v_env_80_);
lean_ctor_set(v_reuseFailAlloc_114_, 1, v_nextMacroScope_81_);
lean_ctor_set(v_reuseFailAlloc_114_, 2, v_ngen_82_);
lean_ctor_set(v_reuseFailAlloc_114_, 3, v_auxDeclNGen_83_);
lean_ctor_set(v_reuseFailAlloc_114_, 4, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_114_, 5, v_cache_84_);
lean_ctor_set(v_reuseFailAlloc_114_, 6, v_messages_85_);
lean_ctor_set(v_reuseFailAlloc_114_, 7, v_infoState_86_);
lean_ctor_set(v_reuseFailAlloc_114_, 8, v_snapshotTasks_87_);
v___x_108_ = v_reuseFailAlloc_114_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_112_; 
v___x_109_ = lean_st_ref_set(v___y_70_, v___x_108_);
v___x_110_ = lean_box(0);
if (v_isShared_77_ == 0)
{
lean_ctor_set(v___x_76_, 0, v___x_110_);
v___x_112_ = v___x_76_;
goto v_reusejp_111_;
}
else
{
lean_object* v_reuseFailAlloc_113_; 
v_reuseFailAlloc_113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_113_, 0, v___x_110_);
v___x_112_ = v_reuseFailAlloc_113_;
goto v_reusejp_111_;
}
v_reusejp_111_:
{
return v___x_112_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0___boxed(lean_object* v_cls_119_, lean_object* v_msg_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_, lean_object* v___y_124_, lean_object* v___y_125_){
_start:
{
lean_object* v_res_126_; 
v_res_126_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0(v_cls_119_, v_msg_120_, v___y_121_, v___y_122_, v___y_123_, v___y_124_);
lean_dec(v___y_124_);
lean_dec_ref(v___y_123_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
return v_res_126_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__7(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4));
v___x_140_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__6));
v___x_141_ = l_Lean_Name_append(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__9(void){
_start:
{
lean_object* v___x_143_; lean_object* v___x_144_; 
v___x_143_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__8));
v___x_144_ = l_Lean_stringToMessageData(v___x_143_);
return v___x_144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force(lean_object* v_ref_145_, lean_object* v_m_146_, lean_object* v_a_147_, lean_object* v_a_148_, lean_object* v_a_149_, lean_object* v_a_150_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = lean_st_ref_get(v_ref_145_);
if (lean_obj_tag(v___x_152_) == 0)
{
lean_object* v_elabFn_153_; lean_object* v___x_155_; uint8_t v_isShared_156_; uint8_t v_isSharedCheck_190_; 
v_elabFn_153_ = lean_ctor_get(v___x_152_, 0);
v_isSharedCheck_190_ = !lean_is_exclusive(v___x_152_);
if (v_isSharedCheck_190_ == 0)
{
v___x_155_ = v___x_152_;
v_isShared_156_ = v_isSharedCheck_190_;
goto v_resetjp_154_;
}
else
{
lean_inc(v_elabFn_153_);
lean_dec(v___x_152_);
v___x_155_ = lean_box(0);
v_isShared_156_ = v_isSharedCheck_190_;
goto v_resetjp_154_;
}
v_resetjp_154_:
{
lean_object* v___x_157_; 
lean_inc(v_a_150_);
lean_inc_ref(v_a_149_);
lean_inc(v_a_148_);
lean_inc_ref(v_a_147_);
v___x_157_ = lean_apply_6(v_elabFn_153_, v_m_146_, v_a_147_, v_a_148_, v_a_149_, v_a_150_, lean_box(0));
if (lean_obj_tag(v___x_157_) == 0)
{
lean_object* v_a_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_189_; 
v_a_158_ = lean_ctor_get(v___x_157_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_157_);
if (v_isSharedCheck_189_ == 0)
{
v___x_160_ = v___x_157_;
v_isShared_161_ = v_isSharedCheck_189_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_a_158_);
lean_dec(v___x_157_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_189_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v_options_170_; uint8_t v_hasTrace_171_; 
v_options_170_ = lean_ctor_get(v_a_149_, 2);
v_hasTrace_171_ = lean_ctor_get_uint8(v_options_170_, sizeof(void*)*1);
if (v_hasTrace_171_ == 0)
{
goto v___jp_162_;
}
else
{
lean_object* v_inheritedTraceOptions_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v_inheritedTraceOptions_172_ = lean_ctor_get(v_a_149_, 13);
v___x_173_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__4));
v___x_174_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__7, &l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__7_once, _init_l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__7);
v___x_175_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_172_, v_options_170_, v___x_174_);
if (v___x_175_ == 0)
{
goto v___jp_162_;
}
else
{
lean_object* v_pattern_176_; lean_object* v___x_177_; lean_object* v___x_178_; lean_object* v___x_179_; lean_object* v___x_180_; 
v_pattern_176_ = lean_ctor_get(v_a_158_, 3);
v___x_177_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__9, &l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__9_once, _init_l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___closed__9);
lean_inc_ref(v_pattern_176_);
v___x_178_ = l_Lean_MessageData_ofExpr(v_pattern_176_);
v___x_179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_179_, 0, v___x_177_);
lean_ctor_set(v___x_179_, 1, v___x_178_);
v___x_180_ = l_Lean_addTrace___at___00Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force_spec__0(v___x_173_, v___x_179_, v_a_147_, v_a_148_, v_a_149_, v_a_150_);
if (lean_obj_tag(v___x_180_) == 0)
{
lean_dec_ref_known(v___x_180_, 1);
goto v___jp_162_;
}
else
{
lean_object* v_a_181_; lean_object* v___x_183_; uint8_t v_isShared_184_; uint8_t v_isSharedCheck_188_; 
lean_del_object(v___x_160_);
lean_dec(v_a_158_);
lean_del_object(v___x_155_);
v_a_181_ = lean_ctor_get(v___x_180_, 0);
v_isSharedCheck_188_ = !lean_is_exclusive(v___x_180_);
if (v_isSharedCheck_188_ == 0)
{
v___x_183_ = v___x_180_;
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
else
{
lean_inc(v_a_181_);
lean_dec(v___x_180_);
v___x_183_ = lean_box(0);
v_isShared_184_ = v_isSharedCheck_188_;
goto v_resetjp_182_;
}
v_resetjp_182_:
{
lean_object* v___x_186_; 
if (v_isShared_184_ == 0)
{
v___x_186_ = v___x_183_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v_a_181_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
v___jp_162_:
{
lean_object* v___x_164_; 
lean_inc(v_a_158_);
if (v_isShared_156_ == 0)
{
lean_ctor_set_tag(v___x_155_, 1);
lean_ctor_set(v___x_155_, 0, v_a_158_);
v___x_164_ = v___x_155_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_169_; 
v_reuseFailAlloc_169_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_169_, 0, v_a_158_);
v___x_164_ = v_reuseFailAlloc_169_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = lean_st_ref_set(v_ref_145_, v___x_164_);
if (v_isShared_161_ == 0)
{
v___x_167_ = v___x_160_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v_a_158_);
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
}
else
{
lean_del_object(v___x_155_);
return v___x_157_;
}
}
}
else
{
lean_object* v_pat_191_; lean_object* v___x_192_; 
lean_dec_ref(v_m_146_);
v_pat_191_ = lean_ctor_get(v___x_152_, 0);
lean_inc_ref(v_pat_191_);
lean_dec_ref_known(v___x_152_, 1);
v___x_192_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_192_, 0, v_pat_191_);
return v___x_192_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force___boxed(lean_object* v_ref_193_, lean_object* v_m_194_, lean_object* v_a_195_, lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Elab_Tactic_Do_Internal_UntilPatternThunk_force(v_ref_193_, v_m_194_, v_a_195_, v_a_196_, v_a_197_, v_a_198_);
lean_dec(v_a_198_);
lean_dec_ref(v_a_197_);
lean_dec(v_a_196_);
lean_dec_ref(v_a_195_);
lean_dec(v_ref_193_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(lean_object* v_info_201_){
_start:
{
lean_object* v_args_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; 
v_args_202_ = lean_ctor_get(v_info_201_, 1);
v___x_203_ = l_Lean_instInhabitedExpr;
v___x_204_ = lean_unsigned_to_nat(0u);
v___x_205_ = lean_array_get_borrowed(v___x_203_, v_args_202_, v___x_204_);
lean_inc(v___x_205_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m___boxed(lean_object* v_info_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_m(v_info_206_);
lean_dec_ref(v_info_206_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(lean_object* v_info_208_){
_start:
{
lean_object* v_args_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
v_args_209_ = lean_ctor_get(v_info_208_, 1);
v___x_210_ = l_Lean_instInhabitedExpr;
v___x_211_ = lean_unsigned_to_nat(1u);
v___x_212_ = lean_array_get_borrowed(v___x_210_, v_args_209_, v___x_211_);
lean_inc(v___x_212_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred___boxed(lean_object* v_info_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_Pred(v_info_213_);
lean_dec_ref(v_info_213_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_EPred(lean_object* v_info_215_){
_start:
{
lean_object* v_args_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_args_216_ = lean_ctor_get(v_info_215_, 1);
v___x_217_ = l_Lean_instInhabitedExpr;
v___x_218_ = lean_unsigned_to_nat(2u);
v___x_219_ = lean_array_get_borrowed(v___x_217_, v_args_216_, v___x_218_);
lean_inc(v___x_219_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_EPred___boxed(lean_object* v_info_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_EPred(v_info_220_);
lean_dec_ref(v_info_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(lean_object* v_info_222_){
_start:
{
lean_object* v_args_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_args_223_ = lean_ctor_get(v_info_222_, 1);
v___x_224_ = l_Lean_instInhabitedExpr;
v___x_225_ = lean_unsigned_to_nat(6u);
v___x_226_ = lean_array_get_borrowed(v___x_224_, v_args_223_, v___x_225_);
lean_inc(v___x_226_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP___boxed(lean_object* v_info_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_instWP(v_info_227_);
lean_dec_ref(v_info_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(lean_object* v_info_229_){
_start:
{
lean_object* v_args_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_args_230_ = lean_ctor_get(v_info_229_, 1);
v___x_231_ = l_Lean_instInhabitedExpr;
v___x_232_ = lean_unsigned_to_nat(8u);
v___x_233_ = lean_array_get_borrowed(v___x_231_, v_args_230_, v___x_232_);
lean_inc(v___x_233_);
return v___x_233_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog___boxed(lean_object* v_info_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_WPInfo_prog(v_info_234_);
lean_dec_ref(v_info_234_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(lean_object* v_a_292_, lean_object* v_a_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__4));
v___x_298_ = lean_box(0);
v___x_299_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_297_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_299_) == 0)
{
lean_object* v_a_300_; lean_object* v___x_301_; lean_object* v___x_302_; 
v_a_300_ = lean_ctor_get(v___x_299_, 0);
lean_inc(v_a_300_);
lean_dec_ref_known(v___x_299_, 1);
v___x_301_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__8));
v___x_302_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_301_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_302_) == 0)
{
lean_object* v_a_303_; lean_object* v___x_304_; lean_object* v___x_305_; 
v_a_303_ = lean_ctor_get(v___x_302_, 0);
lean_inc(v_a_303_);
lean_dec_ref_known(v___x_302_, 1);
v___x_304_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__10));
v___x_305_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_304_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_305_) == 0)
{
lean_object* v_a_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v_a_306_ = lean_ctor_get(v___x_305_, 0);
lean_inc(v_a_306_);
lean_dec_ref_known(v___x_305_, 1);
v___x_307_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__12));
v___x_308_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_307_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_a_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_a_309_ = lean_ctor_get(v___x_308_, 0);
lean_inc(v_a_309_);
lean_dec_ref_known(v___x_308_, 1);
v___x_310_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__14));
v___x_311_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_310_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_311_) == 0)
{
lean_object* v_a_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_a_312_ = lean_ctor_get(v___x_311_, 0);
lean_inc(v_a_312_);
lean_dec_ref_known(v___x_311_, 1);
v___x_313_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__16));
v___x_314_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_313_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_314_) == 0)
{
lean_object* v_a_315_; lean_object* v___x_316_; lean_object* v___x_317_; 
v_a_315_ = lean_ctor_get(v___x_314_, 0);
lean_inc(v_a_315_);
lean_dec_ref_known(v___x_314_, 1);
v___x_316_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__18));
v___x_317_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_316_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_317_) == 0)
{
lean_object* v_a_318_; lean_object* v___x_319_; lean_object* v___x_320_; 
v_a_318_ = lean_ctor_get(v___x_317_, 0);
lean_inc(v_a_318_);
lean_dec_ref_known(v___x_317_, 1);
v___x_319_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__21));
v___x_320_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_319_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_320_) == 0)
{
lean_object* v_a_321_; lean_object* v___x_322_; lean_object* v___x_323_; 
v_a_321_ = lean_ctor_get(v___x_320_, 0);
lean_inc(v_a_321_);
lean_dec_ref_known(v___x_320_, 1);
v___x_322_ = ((lean_object*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___closed__24));
v___x_323_ = l_Lean_Meta_Sym_mkBackwardRuleFromDecl(v___x_322_, v___x_298_, v_a_292_, v_a_293_, v_a_294_, v_a_295_);
if (lean_obj_tag(v___x_323_) == 0)
{
lean_object* v_a_324_; lean_object* v___x_326_; uint8_t v_isShared_327_; uint8_t v_isSharedCheck_332_; 
v_a_324_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_332_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_332_ == 0)
{
v___x_326_ = v___x_323_;
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
else
{
lean_inc(v_a_324_);
lean_dec(v___x_323_);
v___x_326_ = lean_box(0);
v_isShared_327_ = v_isSharedCheck_332_;
goto v_resetjp_325_;
}
v_resetjp_325_:
{
lean_object* v___x_328_; lean_object* v___x_330_; 
v___x_328_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v___x_328_, 0, v_a_300_);
lean_ctor_set(v___x_328_, 1, v_a_303_);
lean_ctor_set(v___x_328_, 2, v_a_306_);
lean_ctor_set(v___x_328_, 3, v_a_309_);
lean_ctor_set(v___x_328_, 4, v_a_312_);
lean_ctor_set(v___x_328_, 5, v_a_315_);
lean_ctor_set(v___x_328_, 6, v_a_318_);
lean_ctor_set(v___x_328_, 7, v_a_321_);
lean_ctor_set(v___x_328_, 8, v_a_324_);
if (v_isShared_327_ == 0)
{
lean_ctor_set(v___x_326_, 0, v___x_328_);
v___x_330_ = v___x_326_;
goto v_reusejp_329_;
}
else
{
lean_object* v_reuseFailAlloc_331_; 
v_reuseFailAlloc_331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_331_, 0, v___x_328_);
v___x_330_ = v_reuseFailAlloc_331_;
goto v_reusejp_329_;
}
v_reusejp_329_:
{
return v___x_330_;
}
}
}
else
{
lean_object* v_a_333_; lean_object* v___x_335_; uint8_t v_isShared_336_; uint8_t v_isSharedCheck_340_; 
lean_dec(v_a_321_);
lean_dec(v_a_318_);
lean_dec(v_a_315_);
lean_dec(v_a_312_);
lean_dec(v_a_309_);
lean_dec(v_a_306_);
lean_dec(v_a_303_);
lean_dec(v_a_300_);
v_a_333_ = lean_ctor_get(v___x_323_, 0);
v_isSharedCheck_340_ = !lean_is_exclusive(v___x_323_);
if (v_isSharedCheck_340_ == 0)
{
v___x_335_ = v___x_323_;
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
else
{
lean_inc(v_a_333_);
lean_dec(v___x_323_);
v___x_335_ = lean_box(0);
v_isShared_336_ = v_isSharedCheck_340_;
goto v_resetjp_334_;
}
v_resetjp_334_:
{
lean_object* v___x_338_; 
if (v_isShared_336_ == 0)
{
v___x_338_ = v___x_335_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_339_; 
v_reuseFailAlloc_339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_339_, 0, v_a_333_);
v___x_338_ = v_reuseFailAlloc_339_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
return v___x_338_;
}
}
}
}
else
{
lean_object* v_a_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_348_; 
lean_dec(v_a_318_);
lean_dec(v_a_315_);
lean_dec(v_a_312_);
lean_dec(v_a_309_);
lean_dec(v_a_306_);
lean_dec(v_a_303_);
lean_dec(v_a_300_);
v_a_341_ = lean_ctor_get(v___x_320_, 0);
v_isSharedCheck_348_ = !lean_is_exclusive(v___x_320_);
if (v_isSharedCheck_348_ == 0)
{
v___x_343_ = v___x_320_;
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_a_341_);
lean_dec(v___x_320_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_348_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
lean_object* v___x_346_; 
if (v_isShared_344_ == 0)
{
v___x_346_ = v___x_343_;
goto v_reusejp_345_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v_a_341_);
v___x_346_ = v_reuseFailAlloc_347_;
goto v_reusejp_345_;
}
v_reusejp_345_:
{
return v___x_346_;
}
}
}
}
else
{
lean_object* v_a_349_; lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_356_; 
lean_dec(v_a_315_);
lean_dec(v_a_312_);
lean_dec(v_a_309_);
lean_dec(v_a_306_);
lean_dec(v_a_303_);
lean_dec(v_a_300_);
v_a_349_ = lean_ctor_get(v___x_317_, 0);
v_isSharedCheck_356_ = !lean_is_exclusive(v___x_317_);
if (v_isSharedCheck_356_ == 0)
{
v___x_351_ = v___x_317_;
v_isShared_352_ = v_isSharedCheck_356_;
goto v_resetjp_350_;
}
else
{
lean_inc(v_a_349_);
lean_dec(v___x_317_);
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
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_a_312_);
lean_dec(v_a_309_);
lean_dec(v_a_306_);
lean_dec(v_a_303_);
lean_dec(v_a_300_);
v_a_357_ = lean_ctor_get(v___x_314_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_314_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_314_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_314_);
v___x_359_ = lean_box(0);
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
v_resetjp_358_:
{
lean_object* v___x_362_; 
if (v_isShared_360_ == 0)
{
v___x_362_ = v___x_359_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v_a_357_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
else
{
lean_object* v_a_365_; lean_object* v___x_367_; uint8_t v_isShared_368_; uint8_t v_isSharedCheck_372_; 
lean_dec(v_a_309_);
lean_dec(v_a_306_);
lean_dec(v_a_303_);
lean_dec(v_a_300_);
v_a_365_ = lean_ctor_get(v___x_311_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_311_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_311_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_311_);
v___x_367_ = lean_box(0);
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
v_resetjp_366_:
{
lean_object* v___x_370_; 
if (v_isShared_368_ == 0)
{
v___x_370_ = v___x_367_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_a_365_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
return v___x_370_;
}
}
}
}
else
{
lean_object* v_a_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_380_; 
lean_dec(v_a_306_);
lean_dec(v_a_303_);
lean_dec(v_a_300_);
v_a_373_ = lean_ctor_get(v___x_308_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_308_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_308_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_378_; 
if (v_isShared_376_ == 0)
{
v___x_378_ = v___x_375_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_a_373_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
else
{
lean_object* v_a_381_; lean_object* v___x_383_; uint8_t v_isShared_384_; uint8_t v_isSharedCheck_388_; 
lean_dec(v_a_303_);
lean_dec(v_a_300_);
v_a_381_ = lean_ctor_get(v___x_305_, 0);
v_isSharedCheck_388_ = !lean_is_exclusive(v___x_305_);
if (v_isSharedCheck_388_ == 0)
{
v___x_383_ = v___x_305_;
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
else
{
lean_inc(v_a_381_);
lean_dec(v___x_305_);
v___x_383_ = lean_box(0);
v_isShared_384_ = v_isSharedCheck_388_;
goto v_resetjp_382_;
}
v_resetjp_382_:
{
lean_object* v___x_386_; 
if (v_isShared_384_ == 0)
{
v___x_386_ = v___x_383_;
goto v_reusejp_385_;
}
else
{
lean_object* v_reuseFailAlloc_387_; 
v_reuseFailAlloc_387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_387_, 0, v_a_381_);
v___x_386_ = v_reuseFailAlloc_387_;
goto v_reusejp_385_;
}
v_reusejp_385_:
{
return v___x_386_;
}
}
}
}
else
{
lean_object* v_a_389_; lean_object* v___x_391_; uint8_t v_isShared_392_; uint8_t v_isSharedCheck_396_; 
lean_dec(v_a_300_);
v_a_389_ = lean_ctor_get(v___x_302_, 0);
v_isSharedCheck_396_ = !lean_is_exclusive(v___x_302_);
if (v_isSharedCheck_396_ == 0)
{
v___x_391_ = v___x_302_;
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
else
{
lean_inc(v_a_389_);
lean_dec(v___x_302_);
v___x_391_ = lean_box(0);
v_isShared_392_ = v_isSharedCheck_396_;
goto v_resetjp_390_;
}
v_resetjp_390_:
{
lean_object* v___x_394_; 
if (v_isShared_392_ == 0)
{
v___x_394_ = v___x_391_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_395_; 
v_reuseFailAlloc_395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_395_, 0, v_a_389_);
v___x_394_ = v_reuseFailAlloc_395_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
return v___x_394_;
}
}
}
}
else
{
lean_object* v_a_397_; lean_object* v___x_399_; uint8_t v_isShared_400_; uint8_t v_isSharedCheck_404_; 
v_a_397_ = lean_ctor_get(v___x_299_, 0);
v_isSharedCheck_404_ = !lean_is_exclusive(v___x_299_);
if (v_isSharedCheck_404_ == 0)
{
v___x_399_ = v___x_299_;
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
else
{
lean_inc(v_a_397_);
lean_dec(v___x_299_);
v___x_399_ = lean_box(0);
v_isShared_400_ = v_isSharedCheck_404_;
goto v_resetjp_398_;
}
v_resetjp_398_:
{
lean_object* v___x_402_; 
if (v_isShared_400_ == 0)
{
v___x_402_ = v___x_399_;
goto v_reusejp_401_;
}
else
{
lean_object* v_reuseFailAlloc_403_; 
v_reuseFailAlloc_403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_403_, 0, v_a_397_);
v___x_402_ = v_reuseFailAlloc_403_;
goto v_reusejp_401_;
}
v_reusejp_401_:
{
return v___x_402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules___boxed(lean_object* v_a_405_, lean_object* v_a_406_, lean_object* v_a_407_, lean_object* v_a_408_, lean_object* v_a_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_mkBackwardRules(v_a_405_, v_a_406_, v_a_407_, v_a_408_);
lean_dec(v_a_408_);
lean_dec_ref(v_a_407_);
lean_dec(v_a_406_);
lean_dec_ref(v_a_405_);
return v_res_410_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0(void){
_start:
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_411_ = lean_unsigned_to_nat(0u);
v___x_412_ = lean_box(0);
v___x_413_ = lean_box(1);
v___x_414_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_instInhabitedSpecTheorems_default;
v___x_415_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_415_, 0, v___x_414_);
lean_ctor_set(v___x_415_, 1, v___x_413_);
lean_ctor_set(v___x_415_, 2, v___x_412_);
lean_ctor_set(v___x_415_, 3, v___x_411_);
return v___x_415_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default(void){
_start:
{
lean_object* v___x_416_; 
v___x_416_ = lean_obj_once(&l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0, &l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0_once, _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default___closed__0);
return v___x_416_;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope(void){
_start:
{
lean_object* v___x_417_; 
v___x_417_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_instInhabitedScope_default;
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_registerJP(lean_object* v_s_418_, lean_object* v_fv_419_, lean_object* v_info_420_){
_start:
{
lean_object* v_specs_421_; lean_object* v_jps_422_; lean_object* v_lastLiftedPre_x3f_423_; lean_object* v_nextDeclIdx_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_432_; 
v_specs_421_ = lean_ctor_get(v_s_418_, 0);
v_jps_422_ = lean_ctor_get(v_s_418_, 1);
v_lastLiftedPre_x3f_423_ = lean_ctor_get(v_s_418_, 2);
v_nextDeclIdx_424_ = lean_ctor_get(v_s_418_, 3);
v_isSharedCheck_432_ = !lean_is_exclusive(v_s_418_);
if (v_isSharedCheck_432_ == 0)
{
v___x_426_ = v_s_418_;
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_nextDeclIdx_424_);
lean_inc(v_lastLiftedPre_x3f_423_);
lean_inc(v_jps_422_);
lean_inc(v_specs_421_);
lean_dec(v_s_418_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_432_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v___x_428_; lean_object* v___x_430_; 
v___x_428_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_instSingletonFVarIdFVarIdSet_spec__1___redArg(v_fv_419_, v_info_420_, v_jps_422_);
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_428_);
v___x_430_ = v___x_426_;
goto v_reusejp_429_;
}
else
{
lean_object* v_reuseFailAlloc_431_; 
v_reuseFailAlloc_431_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_431_, 0, v_specs_421_);
lean_ctor_set(v_reuseFailAlloc_431_, 1, v___x_428_);
lean_ctor_set(v_reuseFailAlloc_431_, 2, v_lastLiftedPre_x3f_423_);
lean_ctor_set(v_reuseFailAlloc_431_, 3, v_nextDeclIdx_424_);
v___x_430_ = v_reuseFailAlloc_431_;
goto v_reusejp_429_;
}
v_reusejp_429_:
{
return v___x_430_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(lean_object* v_t_433_, lean_object* v_k_434_){
_start:
{
if (lean_obj_tag(v_t_433_) == 0)
{
lean_object* v_k_435_; lean_object* v_v_436_; lean_object* v_l_437_; lean_object* v_r_438_; uint8_t v___x_439_; 
v_k_435_ = lean_ctor_get(v_t_433_, 1);
v_v_436_ = lean_ctor_get(v_t_433_, 2);
v_l_437_ = lean_ctor_get(v_t_433_, 3);
v_r_438_ = lean_ctor_get(v_t_433_, 4);
v___x_439_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_434_, v_k_435_);
switch(v___x_439_)
{
case 0:
{
v_t_433_ = v_l_437_;
goto _start;
}
case 1:
{
lean_object* v___x_441_; 
lean_inc(v_v_436_);
v___x_441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_441_, 0, v_v_436_);
return v___x_441_;
}
default: 
{
v_t_433_ = v_r_438_;
goto _start;
}
}
}
else
{
lean_object* v___x_443_; 
v___x_443_ = lean_box(0);
return v___x_443_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg___boxed(lean_object* v_t_444_, lean_object* v_k_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_444_, v_k_445_);
lean_dec(v_k_445_);
lean_dec(v_t_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(lean_object* v_s_447_, lean_object* v_fv_448_){
_start:
{
lean_object* v_jps_449_; lean_object* v___x_450_; 
v_jps_449_ = lean_ctor_get(v_s_447_, 1);
v___x_450_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_jps_449_, v_fv_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f___boxed(lean_object* v_s_451_, lean_object* v_fv_452_){
_start:
{
lean_object* v_res_453_; 
v_res_453_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f(v_s_451_, v_fv_452_);
lean_dec(v_fv_452_);
lean_dec_ref(v_s_451_);
return v_res_453_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(lean_object* v_00_u03b4_454_, lean_object* v_t_455_, lean_object* v_k_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___redArg(v_t_455_, v_k_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0___boxed(lean_object* v_00_u03b4_458_, lean_object* v_t_459_, lean_object* v_k_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_knownJP_x3f_spec__0(v_00_u03b4_458_, v_t_459_, v_k_460_);
lean_dec(v_k_460_);
lean_dec(v_t_459_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(lean_object* v_s_462_, lean_object* v_thm_463_){
_start:
{
lean_object* v_specs_464_; lean_object* v_jps_465_; lean_object* v_lastLiftedPre_x3f_466_; lean_object* v_nextDeclIdx_467_; lean_object* v___x_469_; uint8_t v_isShared_470_; uint8_t v_isSharedCheck_475_; 
v_specs_464_ = lean_ctor_get(v_s_462_, 0);
v_jps_465_ = lean_ctor_get(v_s_462_, 1);
v_lastLiftedPre_x3f_466_ = lean_ctor_get(v_s_462_, 2);
v_nextDeclIdx_467_ = lean_ctor_get(v_s_462_, 3);
v_isSharedCheck_475_ = !lean_is_exclusive(v_s_462_);
if (v_isSharedCheck_475_ == 0)
{
v___x_469_ = v_s_462_;
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
else
{
lean_inc(v_nextDeclIdx_467_);
lean_inc(v_lastLiftedPre_x3f_466_);
lean_inc(v_jps_465_);
lean_inc(v_specs_464_);
lean_dec(v_s_462_);
v___x_469_ = lean_box(0);
v_isShared_470_ = v_isSharedCheck_475_;
goto v_resetjp_468_;
}
v_resetjp_468_:
{
lean_object* v___x_471_; lean_object* v___x_473_; 
v___x_471_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_SpecTheorems_insert(v_specs_464_, v_thm_463_);
if (v_isShared_470_ == 0)
{
lean_ctor_set(v___x_469_, 0, v___x_471_);
v___x_473_ = v___x_469_;
goto v_reusejp_472_;
}
else
{
lean_object* v_reuseFailAlloc_474_; 
v_reuseFailAlloc_474_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_474_, 0, v___x_471_);
lean_ctor_set(v_reuseFailAlloc_474_, 1, v_jps_465_);
lean_ctor_set(v_reuseFailAlloc_474_, 2, v_lastLiftedPre_x3f_466_);
lean_ctor_set(v_reuseFailAlloc_474_, 3, v_nextDeclIdx_467_);
v___x_473_ = v_reuseFailAlloc_474_;
goto v_reusejp_472_;
}
v_reusejp_472_:
{
return v___x_473_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(lean_object* v_x_476_, lean_object* v___y_477_, lean_object* v___y_478_, lean_object* v___y_479_, lean_object* v___y_480_, lean_object* v___y_481_, lean_object* v___y_482_, lean_object* v___y_483_, lean_object* v___y_484_, lean_object* v___y_485_, lean_object* v___y_486_, lean_object* v___y_487_){
_start:
{
lean_object* v___x_489_; 
lean_inc(v___y_483_);
lean_inc_ref(v___y_482_);
lean_inc(v___y_481_);
lean_inc_ref(v___y_480_);
lean_inc(v___y_479_);
lean_inc(v___y_478_);
lean_inc_ref(v___y_477_);
v___x_489_ = lean_apply_12(v_x_476_, v___y_477_, v___y_478_, v___y_479_, v___y_480_, v___y_481_, v___y_482_, v___y_483_, v___y_484_, v___y_485_, v___y_486_, v___y_487_, lean_box(0));
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed(lean_object* v_x_490_, lean_object* v___y_491_, lean_object* v___y_492_, lean_object* v___y_493_, lean_object* v___y_494_, lean_object* v___y_495_, lean_object* v___y_496_, lean_object* v___y_497_, lean_object* v___y_498_, lean_object* v___y_499_, lean_object* v___y_500_, lean_object* v___y_501_, lean_object* v___y_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0(v_x_490_, v___y_491_, v___y_492_, v___y_493_, v___y_494_, v___y_495_, v___y_496_, v___y_497_, v___y_498_, v___y_499_, v___y_500_, v___y_501_);
lean_dec(v___y_497_);
lean_dec_ref(v___y_496_);
lean_dec(v___y_495_);
lean_dec_ref(v___y_494_);
lean_dec(v___y_493_);
lean_dec(v___y_492_);
lean_dec_ref(v___y_491_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(lean_object* v_mvarId_504_, lean_object* v_x_505_, lean_object* v___y_506_, lean_object* v___y_507_, lean_object* v___y_508_, lean_object* v___y_509_, lean_object* v___y_510_, lean_object* v___y_511_, lean_object* v___y_512_, lean_object* v___y_513_, lean_object* v___y_514_, lean_object* v___y_515_, lean_object* v___y_516_){
_start:
{
lean_object* v___f_518_; lean_object* v___x_519_; 
lean_inc(v___y_512_);
lean_inc_ref(v___y_511_);
lean_inc(v___y_510_);
lean_inc_ref(v___y_509_);
lean_inc(v___y_508_);
lean_inc(v___y_507_);
lean_inc_ref(v___y_506_);
v___f_518_ = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_518_, 0, v_x_505_);
lean_closure_set(v___f_518_, 1, v___y_506_);
lean_closure_set(v___f_518_, 2, v___y_507_);
lean_closure_set(v___f_518_, 3, v___y_508_);
lean_closure_set(v___f_518_, 4, v___y_509_);
lean_closure_set(v___f_518_, 5, v___y_510_);
lean_closure_set(v___f_518_, 6, v___y_511_);
lean_closure_set(v___f_518_, 7, v___y_512_);
v___x_519_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_504_, v___f_518_, v___y_513_, v___y_514_, v___y_515_, v___y_516_);
if (lean_obj_tag(v___x_519_) == 0)
{
return v___x_519_;
}
else
{
lean_object* v_a_520_; lean_object* v___x_522_; uint8_t v_isShared_523_; uint8_t v_isSharedCheck_527_; 
v_a_520_ = lean_ctor_get(v___x_519_, 0);
v_isSharedCheck_527_ = !lean_is_exclusive(v___x_519_);
if (v_isSharedCheck_527_ == 0)
{
v___x_522_ = v___x_519_;
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
else
{
lean_inc(v_a_520_);
lean_dec(v___x_519_);
v___x_522_ = lean_box(0);
v_isShared_523_ = v_isSharedCheck_527_;
goto v_resetjp_521_;
}
v_resetjp_521_:
{
lean_object* v___x_525_; 
if (v_isShared_523_ == 0)
{
v___x_525_ = v___x_522_;
goto v_reusejp_524_;
}
else
{
lean_object* v_reuseFailAlloc_526_; 
v_reuseFailAlloc_526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_526_, 0, v_a_520_);
v___x_525_ = v_reuseFailAlloc_526_;
goto v_reusejp_524_;
}
v_reusejp_524_:
{
return v___x_525_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg___boxed(lean_object* v_mvarId_528_, lean_object* v_x_529_, lean_object* v___y_530_, lean_object* v___y_531_, lean_object* v___y_532_, lean_object* v___y_533_, lean_object* v___y_534_, lean_object* v___y_535_, lean_object* v___y_536_, lean_object* v___y_537_, lean_object* v___y_538_, lean_object* v___y_539_, lean_object* v___y_540_, lean_object* v___y_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_528_, v_x_529_, v___y_530_, v___y_531_, v___y_532_, v___y_533_, v___y_534_, v___y_535_, v___y_536_, v___y_537_, v___y_538_, v___y_539_, v___y_540_);
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
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(lean_object* v_00_u03b1_543_, lean_object* v_mvarId_544_, lean_object* v_x_545_, lean_object* v___y_546_, lean_object* v___y_547_, lean_object* v___y_548_, lean_object* v___y_549_, lean_object* v___y_550_, lean_object* v___y_551_, lean_object* v___y_552_, lean_object* v___y_553_, lean_object* v___y_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v___x_558_; 
v___x_558_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_mvarId_544_, v_x_545_, v___y_546_, v___y_547_, v___y_548_, v___y_549_, v___y_550_, v___y_551_, v___y_552_, v___y_553_, v___y_554_, v___y_555_, v___y_556_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___boxed(lean_object* v_00_u03b1_559_, lean_object* v_mvarId_560_, lean_object* v_x_561_, lean_object* v___y_562_, lean_object* v___y_563_, lean_object* v___y_564_, lean_object* v___y_565_, lean_object* v___y_566_, lean_object* v___y_567_, lean_object* v___y_568_, lean_object* v___y_569_, lean_object* v___y_570_, lean_object* v___y_571_, lean_object* v___y_572_, lean_object* v___y_573_){
_start:
{
lean_object* v_res_574_; 
v_res_574_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1(v_00_u03b1_559_, v_mvarId_560_, v_x_561_, v___y_562_, v___y_563_, v___y_564_, v___y_565_, v___y_566_, v___y_567_, v___y_568_, v___y_569_, v___y_570_, v___y_571_, v___y_572_);
lean_dec(v___y_572_);
lean_dec_ref(v___y_571_);
lean_dec(v___y_570_);
lean_dec_ref(v___y_569_);
lean_dec(v___y_568_);
lean_dec_ref(v___y_567_);
lean_dec(v___y_566_);
lean_dec_ref(v___y_565_);
lean_dec(v___y_564_);
lean_dec(v___y_563_);
lean_dec_ref(v___y_562_);
return v_res_574_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(lean_object* v_as_575_, size_t v_i_576_, size_t v_stop_577_, lean_object* v_b_578_, lean_object* v___y_579_, lean_object* v___y_580_, lean_object* v___y_581_, lean_object* v___y_582_){
_start:
{
lean_object* v_a_585_; uint8_t v___x_589_; 
v___x_589_ = lean_usize_dec_eq(v_i_576_, v_stop_577_);
if (v___x_589_ == 0)
{
lean_object* v___x_590_; 
v___x_590_ = lean_array_uget_borrowed(v_as_575_, v_i_576_);
if (lean_obj_tag(v___x_590_) == 0)
{
v_a_585_ = v_b_578_;
goto v___jp_584_;
}
else
{
lean_object* v_val_591_; uint8_t v___x_592_; 
v_val_591_ = lean_ctor_get(v___x_590_, 0);
v___x_592_ = l_Lean_LocalDecl_isAuxDecl(v_val_591_);
if (v___x_592_ == 0)
{
lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; 
v___x_593_ = l_Lean_LocalDecl_fvarId(v_val_591_);
v___x_594_ = lean_unsigned_to_nat(100u);
v___x_595_ = l_Lean_Elab_Tactic_Do_Internal_SpecAttr_mkSpecTheoremFromLocal(v___x_593_, v___x_594_, v___y_579_, v___y_580_, v___y_581_, v___y_582_);
if (lean_obj_tag(v___x_595_) == 0)
{
lean_object* v_a_596_; 
v_a_596_ = lean_ctor_get(v___x_595_, 0);
lean_inc(v_a_596_);
lean_dec_ref_known(v___x_595_, 1);
if (lean_obj_tag(v_a_596_) == 1)
{
lean_object* v_val_597_; lean_object* v___x_598_; 
v_val_597_ = lean_ctor_get(v_a_596_, 0);
lean_inc(v_val_597_);
lean_dec_ref_known(v_a_596_, 1);
v___x_598_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_insertSpec(v_b_578_, v_val_597_);
v_a_585_ = v___x_598_;
goto v___jp_584_;
}
else
{
lean_dec(v_a_596_);
v_a_585_ = v_b_578_;
goto v___jp_584_;
}
}
else
{
lean_object* v_a_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_610_; 
v_a_599_ = lean_ctor_get(v___x_595_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_595_);
if (v_isSharedCheck_610_ == 0)
{
v___x_601_ = v___x_595_;
v_isShared_602_ = v_isSharedCheck_610_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_a_599_);
lean_dec(v___x_595_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_610_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
uint8_t v___y_604_; uint8_t v___x_608_; 
v___x_608_ = l_Lean_Exception_isInterrupt(v_a_599_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; 
lean_inc(v_a_599_);
v___x_609_ = l_Lean_Exception_isRuntime(v_a_599_);
v___y_604_ = v___x_609_;
goto v___jp_603_;
}
else
{
v___y_604_ = v___x_608_;
goto v___jp_603_;
}
v___jp_603_:
{
if (v___y_604_ == 0)
{
lean_del_object(v___x_601_);
lean_dec(v_a_599_);
v_a_585_ = v_b_578_;
goto v___jp_584_;
}
else
{
lean_object* v___x_606_; 
lean_dec_ref(v_b_578_);
if (v_isShared_602_ == 0)
{
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_607_; 
v_reuseFailAlloc_607_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_607_, 0, v_a_599_);
v___x_606_ = v_reuseFailAlloc_607_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
return v___x_606_;
}
}
}
}
}
}
else
{
v_a_585_ = v_b_578_;
goto v___jp_584_;
}
}
}
else
{
lean_object* v___x_611_; 
v___x_611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_611_, 0, v_b_578_);
return v___x_611_;
}
v___jp_584_:
{
size_t v___x_586_; size_t v___x_587_; 
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_add(v_i_576_, v___x_586_);
v_i_576_ = v___x_587_;
v_b_578_ = v_a_585_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg___boxed(lean_object* v_as_612_, lean_object* v_i_613_, lean_object* v_stop_614_, lean_object* v_b_615_, lean_object* v___y_616_, lean_object* v___y_617_, lean_object* v___y_618_, lean_object* v___y_619_, lean_object* v___y_620_){
_start:
{
size_t v_i_boxed_621_; size_t v_stop_boxed_622_; lean_object* v_res_623_; 
v_i_boxed_621_ = lean_unbox_usize(v_i_613_);
lean_dec(v_i_613_);
v_stop_boxed_622_ = lean_unbox_usize(v_stop_614_);
lean_dec(v_stop_614_);
v_res_623_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_612_, v_i_boxed_621_, v_stop_boxed_622_, v_b_615_, v___y_616_, v___y_617_, v___y_618_, v___y_619_);
lean_dec(v___y_619_);
lean_dec_ref(v___y_618_);
lean_dec(v___y_617_);
lean_dec_ref(v___y_616_);
lean_dec_ref(v_as_612_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v___y_626_, lean_object* v___y_627_, lean_object* v___y_628_, lean_object* v___y_629_, lean_object* v___y_630_, lean_object* v___y_631_, lean_object* v___y_632_, lean_object* v___y_633_, lean_object* v___y_634_, lean_object* v___y_635_, lean_object* v___y_636_){
_start:
{
if (lean_obj_tag(v_x_624_) == 0)
{
lean_object* v_cs_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_658_; 
v_cs_638_ = lean_ctor_get(v_x_624_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_658_ == 0)
{
v___x_640_ = v_x_624_;
v_isShared_641_ = v_isSharedCheck_658_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_cs_638_);
lean_dec(v_x_624_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_658_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_643_; uint8_t v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(0u);
v___x_643_ = lean_array_get_size(v_cs_638_);
v___x_644_ = lean_nat_dec_lt(v___x_642_, v___x_643_);
if (v___x_644_ == 0)
{
lean_object* v___x_646_; 
lean_dec_ref(v_cs_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_x_625_);
v___x_646_ = v___x_640_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_647_; 
v_reuseFailAlloc_647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_647_, 0, v_x_625_);
v___x_646_ = v_reuseFailAlloc_647_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
return v___x_646_;
}
}
else
{
uint8_t v___x_648_; 
v___x_648_ = lean_nat_dec_le(v___x_643_, v___x_643_);
if (v___x_648_ == 0)
{
if (v___x_644_ == 0)
{
lean_object* v___x_650_; 
lean_dec_ref(v_cs_638_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 0, v_x_625_);
v___x_650_ = v___x_640_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_x_625_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
return v___x_650_;
}
}
else
{
size_t v___x_652_; size_t v___x_653_; lean_object* v___x_654_; 
lean_del_object(v___x_640_);
v___x_652_ = ((size_t)0ULL);
v___x_653_ = lean_usize_of_nat(v___x_643_);
v___x_654_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_638_, v___x_652_, v___x_653_, v_x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_cs_638_);
return v___x_654_;
}
}
else
{
size_t v___x_655_; size_t v___x_656_; lean_object* v___x_657_; 
lean_del_object(v___x_640_);
v___x_655_ = ((size_t)0ULL);
v___x_656_ = lean_usize_of_nat(v___x_643_);
v___x_657_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_638_, v___x_655_, v___x_656_, v_x_625_, v___y_626_, v___y_627_, v___y_628_, v___y_629_, v___y_630_, v___y_631_, v___y_632_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_cs_638_);
return v___x_657_;
}
}
}
}
else
{
lean_object* v_vs_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_679_; 
v_vs_659_ = lean_ctor_get(v_x_624_, 0);
v_isSharedCheck_679_ = !lean_is_exclusive(v_x_624_);
if (v_isSharedCheck_679_ == 0)
{
v___x_661_ = v_x_624_;
v_isShared_662_ = v_isSharedCheck_679_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_vs_659_);
lean_dec(v_x_624_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_679_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; lean_object* v___x_664_; uint8_t v___x_665_; 
v___x_663_ = lean_unsigned_to_nat(0u);
v___x_664_ = lean_array_get_size(v_vs_659_);
v___x_665_ = lean_nat_dec_lt(v___x_663_, v___x_664_);
if (v___x_665_ == 0)
{
lean_object* v___x_667_; 
lean_dec_ref(v_vs_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 0);
lean_ctor_set(v___x_661_, 0, v_x_625_);
v___x_667_ = v___x_661_;
goto v_reusejp_666_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_x_625_);
v___x_667_ = v_reuseFailAlloc_668_;
goto v_reusejp_666_;
}
v_reusejp_666_:
{
return v___x_667_;
}
}
else
{
uint8_t v___x_669_; 
v___x_669_ = lean_nat_dec_le(v___x_664_, v___x_664_);
if (v___x_669_ == 0)
{
if (v___x_665_ == 0)
{
lean_object* v___x_671_; 
lean_dec_ref(v_vs_659_);
if (v_isShared_662_ == 0)
{
lean_ctor_set_tag(v___x_661_, 0);
lean_ctor_set(v___x_661_, 0, v_x_625_);
v___x_671_ = v___x_661_;
goto v_reusejp_670_;
}
else
{
lean_object* v_reuseFailAlloc_672_; 
v_reuseFailAlloc_672_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_672_, 0, v_x_625_);
v___x_671_ = v_reuseFailAlloc_672_;
goto v_reusejp_670_;
}
v_reusejp_670_:
{
return v___x_671_;
}
}
else
{
size_t v___x_673_; size_t v___x_674_; lean_object* v___x_675_; 
lean_del_object(v___x_661_);
v___x_673_ = ((size_t)0ULL);
v___x_674_ = lean_usize_of_nat(v___x_664_);
v___x_675_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_659_, v___x_673_, v___x_674_, v_x_625_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_vs_659_);
return v___x_675_;
}
}
else
{
size_t v___x_676_; size_t v___x_677_; lean_object* v___x_678_; 
lean_del_object(v___x_661_);
v___x_676_ = ((size_t)0ULL);
v___x_677_ = lean_usize_of_nat(v___x_664_);
v___x_678_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_659_, v___x_676_, v___x_677_, v_x_625_, v___y_633_, v___y_634_, v___y_635_, v___y_636_);
lean_dec_ref(v_vs_659_);
return v___x_678_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(lean_object* v_as_680_, size_t v_i_681_, size_t v_stop_682_, lean_object* v_b_683_, lean_object* v___y_684_, lean_object* v___y_685_, lean_object* v___y_686_, lean_object* v___y_687_, lean_object* v___y_688_, lean_object* v___y_689_, lean_object* v___y_690_, lean_object* v___y_691_, lean_object* v___y_692_, lean_object* v___y_693_, lean_object* v___y_694_){
_start:
{
uint8_t v___x_696_; 
v___x_696_ = lean_usize_dec_eq(v_i_681_, v_stop_682_);
if (v___x_696_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = lean_array_uget_borrowed(v_as_680_, v_i_681_);
lean_inc(v___x_697_);
v___x_698_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v___x_697_, v_b_683_, v___y_684_, v___y_685_, v___y_686_, v___y_687_, v___y_688_, v___y_689_, v___y_690_, v___y_691_, v___y_692_, v___y_693_, v___y_694_);
if (lean_obj_tag(v___x_698_) == 0)
{
lean_object* v_a_699_; size_t v___x_700_; size_t v___x_701_; 
v_a_699_ = lean_ctor_get(v___x_698_, 0);
lean_inc(v_a_699_);
lean_dec_ref_known(v___x_698_, 1);
v___x_700_ = ((size_t)1ULL);
v___x_701_ = lean_usize_add(v_i_681_, v___x_700_);
v_i_681_ = v___x_701_;
v_b_683_ = v_a_699_;
goto _start;
}
else
{
return v___x_698_;
}
}
else
{
lean_object* v___x_703_; 
v___x_703_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_703_, 0, v_b_683_);
return v___x_703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3___boxed(lean_object* v_as_704_, lean_object* v_i_705_, lean_object* v_stop_706_, lean_object* v_b_707_, lean_object* v___y_708_, lean_object* v___y_709_, lean_object* v___y_710_, lean_object* v___y_711_, lean_object* v___y_712_, lean_object* v___y_713_, lean_object* v___y_714_, lean_object* v___y_715_, lean_object* v___y_716_, lean_object* v___y_717_, lean_object* v___y_718_, lean_object* v___y_719_){
_start:
{
size_t v_i_boxed_720_; size_t v_stop_boxed_721_; lean_object* v_res_722_; 
v_i_boxed_720_ = lean_unbox_usize(v_i_705_);
lean_dec(v_i_705_);
v_stop_boxed_721_ = lean_unbox_usize(v_stop_706_);
lean_dec(v_stop_706_);
v_res_722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_as_704_, v_i_boxed_720_, v_stop_boxed_721_, v_b_707_, v___y_708_, v___y_709_, v___y_710_, v___y_711_, v___y_712_, v___y_713_, v___y_714_, v___y_715_, v___y_716_, v___y_717_, v___y_718_);
lean_dec(v___y_718_);
lean_dec_ref(v___y_717_);
lean_dec(v___y_716_);
lean_dec_ref(v___y_715_);
lean_dec(v___y_714_);
lean_dec_ref(v___y_713_);
lean_dec(v___y_712_);
lean_dec_ref(v___y_711_);
lean_dec(v___y_710_);
lean_dec(v___y_709_);
lean_dec_ref(v___y_708_);
lean_dec_ref(v_as_704_);
return v_res_722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4___boxed(lean_object* v_x_723_, lean_object* v_x_724_, lean_object* v___y_725_, lean_object* v___y_726_, lean_object* v___y_727_, lean_object* v___y_728_, lean_object* v___y_729_, lean_object* v___y_730_, lean_object* v___y_731_, lean_object* v___y_732_, lean_object* v___y_733_, lean_object* v___y_734_, lean_object* v___y_735_, lean_object* v___y_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_x_723_, v_x_724_, v___y_725_, v___y_726_, v___y_727_, v___y_728_, v___y_729_, v___y_730_, v___y_731_, v___y_732_, v___y_733_, v___y_734_, v___y_735_);
lean_dec(v___y_735_);
lean_dec_ref(v___y_734_);
lean_dec(v___y_733_);
lean_dec_ref(v___y_732_);
lean_dec(v___y_731_);
lean_dec_ref(v___y_730_);
lean_dec(v___y_729_);
lean_dec_ref(v___y_728_);
lean_dec(v___y_727_);
lean_dec(v___y_726_);
lean_dec_ref(v___y_725_);
return v_res_737_;
}
}
static lean_object* _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_738_; 
v___x_738_ = l_Lean_instInhabitedPersistentArrayNode_default(lean_box(0));
return v___x_738_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(lean_object* v_x_739_, size_t v_x_740_, size_t v_x_741_, lean_object* v_x_742_, lean_object* v___y_743_, lean_object* v___y_744_, lean_object* v___y_745_, lean_object* v___y_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
if (lean_obj_tag(v_x_739_) == 0)
{
lean_object* v_cs_755_; lean_object* v___x_756_; size_t v___x_757_; lean_object* v_j_758_; lean_object* v___x_759_; size_t v___x_760_; size_t v___x_761_; size_t v___x_762_; size_t v___x_763_; size_t v___x_764_; size_t v___x_765_; lean_object* v___x_766_; 
v_cs_755_ = lean_ctor_get(v_x_739_, 0);
lean_inc_ref(v_cs_755_);
lean_dec_ref_known(v_x_739_, 1);
v___x_756_ = lean_obj_once(&l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0, &l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0_once, _init_l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___closed__0);
v___x_757_ = lean_usize_shift_right(v_x_740_, v_x_741_);
v_j_758_ = lean_usize_to_nat(v___x_757_);
v___x_759_ = lean_array_get_borrowed(v___x_756_, v_cs_755_, v_j_758_);
v___x_760_ = ((size_t)1ULL);
v___x_761_ = lean_usize_shift_left(v___x_760_, v_x_741_);
v___x_762_ = lean_usize_sub(v___x_761_, v___x_760_);
v___x_763_ = lean_usize_land(v_x_740_, v___x_762_);
v___x_764_ = ((size_t)5ULL);
v___x_765_ = lean_usize_sub(v_x_741_, v___x_764_);
lean_inc(v___x_759_);
v___x_766_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v___x_759_, v___x_763_, v___x_765_, v_x_742_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v_a_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; uint8_t v___x_771_; 
v_a_767_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_a_767_);
v___x_768_ = lean_unsigned_to_nat(1u);
v___x_769_ = lean_nat_add(v_j_758_, v___x_768_);
lean_dec(v_j_758_);
v___x_770_ = lean_array_get_size(v_cs_755_);
v___x_771_ = lean_nat_dec_lt(v___x_769_, v___x_770_);
if (v___x_771_ == 0)
{
lean_dec(v___x_769_);
lean_dec(v_a_767_);
lean_dec_ref(v_cs_755_);
return v___x_766_;
}
else
{
uint8_t v___x_772_; 
v___x_772_ = lean_nat_dec_le(v___x_770_, v___x_770_);
if (v___x_772_ == 0)
{
if (v___x_771_ == 0)
{
lean_dec(v___x_769_);
lean_dec(v_a_767_);
lean_dec_ref(v_cs_755_);
return v___x_766_;
}
else
{
size_t v___x_773_; size_t v___x_774_; lean_object* v___x_775_; 
lean_dec_ref_known(v___x_766_, 1);
v___x_773_ = lean_usize_of_nat(v___x_769_);
lean_dec(v___x_769_);
v___x_774_ = lean_usize_of_nat(v___x_770_);
v___x_775_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_755_, v___x_773_, v___x_774_, v_a_767_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v_cs_755_);
return v___x_775_;
}
}
else
{
size_t v___x_776_; size_t v___x_777_; lean_object* v___x_778_; 
lean_dec_ref_known(v___x_766_, 1);
v___x_776_ = lean_usize_of_nat(v___x_769_);
lean_dec(v___x_769_);
v___x_777_ = lean_usize_of_nat(v___x_770_);
v___x_778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2_spec__3(v_cs_755_, v___x_776_, v___x_777_, v_a_767_, v___y_743_, v___y_744_, v___y_745_, v___y_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v_cs_755_);
return v___x_778_;
}
}
}
else
{
lean_dec(v_j_758_);
lean_dec_ref(v_cs_755_);
return v___x_766_;
}
}
else
{
lean_object* v_vs_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_799_; 
v_vs_779_ = lean_ctor_get(v_x_739_, 0);
v_isSharedCheck_799_ = !lean_is_exclusive(v_x_739_);
if (v_isSharedCheck_799_ == 0)
{
v___x_781_ = v_x_739_;
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_vs_779_);
lean_dec(v_x_739_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_799_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_784_; uint8_t v___x_785_; 
v___x_783_ = lean_usize_to_nat(v_x_740_);
v___x_784_ = lean_array_get_size(v_vs_779_);
v___x_785_ = lean_nat_dec_lt(v___x_783_, v___x_784_);
if (v___x_785_ == 0)
{
lean_object* v___x_787_; 
lean_dec(v___x_783_);
lean_dec_ref(v_vs_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 0);
lean_ctor_set(v___x_781_, 0, v_x_742_);
v___x_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v_x_742_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
else
{
uint8_t v___x_789_; 
v___x_789_ = lean_nat_dec_le(v___x_784_, v___x_784_);
if (v___x_789_ == 0)
{
if (v___x_785_ == 0)
{
lean_object* v___x_791_; 
lean_dec(v___x_783_);
lean_dec_ref(v_vs_779_);
if (v_isShared_782_ == 0)
{
lean_ctor_set_tag(v___x_781_, 0);
lean_ctor_set(v___x_781_, 0, v_x_742_);
v___x_791_ = v___x_781_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v_x_742_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
else
{
size_t v___x_793_; size_t v___x_794_; lean_object* v___x_795_; 
lean_del_object(v___x_781_);
v___x_793_ = lean_usize_of_nat(v___x_783_);
lean_dec(v___x_783_);
v___x_794_ = lean_usize_of_nat(v___x_784_);
v___x_795_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_779_, v___x_793_, v___x_794_, v_x_742_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v_vs_779_);
return v___x_795_;
}
}
else
{
size_t v___x_796_; size_t v___x_797_; lean_object* v___x_798_; 
lean_del_object(v___x_781_);
v___x_796_ = lean_usize_of_nat(v___x_783_);
lean_dec(v___x_783_);
v___x_797_ = lean_usize_of_nat(v___x_784_);
v___x_798_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_vs_779_, v___x_796_, v___x_797_, v_x_742_, v___y_750_, v___y_751_, v___y_752_, v___y_753_);
lean_dec_ref(v_vs_779_);
return v___x_798_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2___boxed(lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_, lean_object* v___y_810_, lean_object* v___y_811_, lean_object* v___y_812_, lean_object* v___y_813_, lean_object* v___y_814_, lean_object* v___y_815_){
_start:
{
size_t v_x_24422__boxed_816_; size_t v_x_24423__boxed_817_; lean_object* v_res_818_; 
v_x_24422__boxed_816_ = lean_unbox_usize(v_x_801_);
lean_dec(v_x_801_);
v_x_24423__boxed_817_ = lean_unbox_usize(v_x_802_);
lean_dec(v_x_802_);
v_res_818_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_x_800_, v_x_24422__boxed_816_, v_x_24423__boxed_817_, v_x_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_, v___y_810_, v___y_811_, v___y_812_, v___y_813_, v___y_814_);
lean_dec(v___y_814_);
lean_dec_ref(v___y_813_);
lean_dec(v___y_812_);
lean_dec_ref(v___y_811_);
lean_dec(v___y_810_);
lean_dec_ref(v___y_809_);
lean_dec(v___y_808_);
lean_dec_ref(v___y_807_);
lean_dec(v___y_806_);
lean_dec(v___y_805_);
lean_dec_ref(v___y_804_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(lean_object* v_t_819_, lean_object* v_init_820_, lean_object* v_start_821_, lean_object* v___y_822_, lean_object* v___y_823_, lean_object* v___y_824_, lean_object* v___y_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = lean_nat_dec_eq(v_start_821_, v___x_834_);
if (v___x_835_ == 0)
{
lean_object* v_root_836_; lean_object* v_tail_837_; size_t v_shift_838_; lean_object* v_tailOff_839_; uint8_t v___x_840_; 
v_root_836_ = lean_ctor_get(v_t_819_, 0);
lean_inc_ref(v_root_836_);
v_tail_837_ = lean_ctor_get(v_t_819_, 1);
lean_inc_ref(v_tail_837_);
v_shift_838_ = lean_ctor_get_usize(v_t_819_, 4);
v_tailOff_839_ = lean_ctor_get(v_t_819_, 3);
lean_inc(v_tailOff_839_);
lean_dec_ref(v_t_819_);
v___x_840_ = lean_nat_dec_le(v_tailOff_839_, v_start_821_);
if (v___x_840_ == 0)
{
size_t v___x_841_; lean_object* v___x_842_; 
lean_dec(v_tailOff_839_);
v___x_841_ = lean_usize_of_nat(v_start_821_);
v___x_842_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlFromMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__2(v_root_836_, v___x_841_, v_shift_838_, v_init_820_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_842_) == 0)
{
lean_object* v_a_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v_a_843_ = lean_ctor_get(v___x_842_, 0);
lean_inc(v_a_843_);
v___x_844_ = lean_array_get_size(v_tail_837_);
v___x_845_ = lean_nat_dec_lt(v___x_834_, v___x_844_);
if (v___x_845_ == 0)
{
lean_dec(v_a_843_);
lean_dec_ref(v_tail_837_);
return v___x_842_;
}
else
{
uint8_t v___x_846_; 
v___x_846_ = lean_nat_dec_le(v___x_844_, v___x_844_);
if (v___x_846_ == 0)
{
if (v___x_845_ == 0)
{
lean_dec(v_a_843_);
lean_dec_ref(v_tail_837_);
return v___x_842_;
}
else
{
size_t v___x_847_; size_t v___x_848_; lean_object* v___x_849_; 
lean_dec_ref_known(v___x_842_, 1);
v___x_847_ = ((size_t)0ULL);
v___x_848_ = lean_usize_of_nat(v___x_844_);
v___x_849_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_837_, v___x_847_, v___x_848_, v_a_843_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec_ref(v_tail_837_);
return v___x_849_;
}
}
else
{
size_t v___x_850_; size_t v___x_851_; lean_object* v___x_852_; 
lean_dec_ref_known(v___x_842_, 1);
v___x_850_ = ((size_t)0ULL);
v___x_851_ = lean_usize_of_nat(v___x_844_);
v___x_852_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_837_, v___x_850_, v___x_851_, v_a_843_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec_ref(v_tail_837_);
return v___x_852_;
}
}
}
else
{
lean_dec_ref(v_tail_837_);
return v___x_842_;
}
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; uint8_t v___x_855_; 
lean_dec_ref(v_root_836_);
v___x_853_ = lean_nat_sub(v_start_821_, v_tailOff_839_);
lean_dec(v_tailOff_839_);
v___x_854_ = lean_array_get_size(v_tail_837_);
v___x_855_ = lean_nat_dec_lt(v___x_853_, v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_dec(v___x_853_);
lean_dec_ref(v_tail_837_);
v___x_856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_856_, 0, v_init_820_);
return v___x_856_;
}
else
{
uint8_t v___x_857_; 
v___x_857_ = lean_nat_dec_le(v___x_854_, v___x_854_);
if (v___x_857_ == 0)
{
if (v___x_855_ == 0)
{
lean_object* v___x_858_; 
lean_dec(v___x_853_);
lean_dec_ref(v_tail_837_);
v___x_858_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_858_, 0, v_init_820_);
return v___x_858_;
}
else
{
size_t v___x_859_; size_t v___x_860_; lean_object* v___x_861_; 
v___x_859_ = lean_usize_of_nat(v___x_853_);
lean_dec(v___x_853_);
v___x_860_ = lean_usize_of_nat(v___x_854_);
v___x_861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_837_, v___x_859_, v___x_860_, v_init_820_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec_ref(v_tail_837_);
return v___x_861_;
}
}
else
{
size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v___x_862_ = lean_usize_of_nat(v___x_853_);
lean_dec(v___x_853_);
v___x_863_ = lean_usize_of_nat(v___x_854_);
v___x_864_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_837_, v___x_862_, v___x_863_, v_init_820_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec_ref(v_tail_837_);
return v___x_864_;
}
}
}
}
else
{
lean_object* v_root_865_; lean_object* v_tail_866_; lean_object* v___x_867_; 
v_root_865_ = lean_ctor_get(v_t_819_, 0);
lean_inc_ref(v_root_865_);
v_tail_866_ = lean_ctor_get(v_t_819_, 1);
lean_inc_ref(v_tail_866_);
lean_dec_ref(v_t_819_);
v___x_867_ = l___private_Lean_Data_PersistentArray_0__Lean_PersistentArray_foldlMAux___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__4(v_root_865_, v_init_820_, v___y_822_, v___y_823_, v___y_824_, v___y_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v_a_868_; lean_object* v___x_869_; uint8_t v___x_870_; 
v_a_868_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_a_868_);
v___x_869_ = lean_array_get_size(v_tail_866_);
v___x_870_ = lean_nat_dec_lt(v___x_834_, v___x_869_);
if (v___x_870_ == 0)
{
lean_dec(v_a_868_);
lean_dec_ref(v_tail_866_);
return v___x_867_;
}
else
{
uint8_t v___x_871_; 
v___x_871_ = lean_nat_dec_le(v___x_869_, v___x_869_);
if (v___x_871_ == 0)
{
if (v___x_870_ == 0)
{
lean_dec(v_a_868_);
lean_dec_ref(v_tail_866_);
return v___x_867_;
}
else
{
size_t v___x_872_; size_t v___x_873_; lean_object* v___x_874_; 
lean_dec_ref_known(v___x_867_, 1);
v___x_872_ = ((size_t)0ULL);
v___x_873_ = lean_usize_of_nat(v___x_869_);
v___x_874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_866_, v___x_872_, v___x_873_, v_a_868_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec_ref(v_tail_866_);
return v___x_874_;
}
}
else
{
size_t v___x_875_; size_t v___x_876_; lean_object* v___x_877_; 
lean_dec_ref_known(v___x_867_, 1);
v___x_875_ = ((size_t)0ULL);
v___x_876_ = lean_usize_of_nat(v___x_869_);
v___x_877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_tail_866_, v___x_875_, v___x_876_, v_a_868_, v___y_829_, v___y_830_, v___y_831_, v___y_832_);
lean_dec_ref(v_tail_866_);
return v___x_877_;
}
}
}
else
{
lean_dec_ref(v_tail_866_);
return v___x_867_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0___boxed(lean_object* v_t_878_, lean_object* v_init_879_, lean_object* v_start_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_, lean_object* v___y_884_, lean_object* v___y_885_, lean_object* v___y_886_, lean_object* v___y_887_, lean_object* v___y_888_, lean_object* v___y_889_, lean_object* v___y_890_, lean_object* v___y_891_, lean_object* v___y_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_t_878_, v_init_879_, v_start_880_, v___y_881_, v___y_882_, v___y_883_, v___y_884_, v___y_885_, v___y_886_, v___y_887_, v___y_888_, v___y_889_, v___y_890_, v___y_891_);
lean_dec(v___y_891_);
lean_dec_ref(v___y_890_);
lean_dec(v___y_889_);
lean_dec_ref(v___y_888_);
lean_dec(v___y_887_);
lean_dec_ref(v___y_886_);
lean_dec(v___y_885_);
lean_dec_ref(v___y_884_);
lean_dec(v___y_883_);
lean_dec(v___y_882_);
lean_dec_ref(v___y_881_);
lean_dec(v_start_880_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(lean_object* v_lctx_894_, lean_object* v_init_895_, lean_object* v_start_896_, lean_object* v___y_897_, lean_object* v___y_898_, lean_object* v___y_899_, lean_object* v___y_900_, lean_object* v___y_901_, lean_object* v___y_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_, lean_object* v___y_907_){
_start:
{
lean_object* v_decls_909_; lean_object* v___x_910_; 
v_decls_909_ = lean_ctor_get(v_lctx_894_, 1);
lean_inc_ref(v_decls_909_);
lean_dec_ref(v_lctx_894_);
v___x_910_ = l_Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0(v_decls_909_, v_init_895_, v_start_896_, v___y_897_, v___y_898_, v___y_899_, v___y_900_, v___y_901_, v___y_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_, v___y_907_);
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0___boxed(lean_object* v_lctx_911_, lean_object* v_init_912_, lean_object* v_start_913_, lean_object* v___y_914_, lean_object* v___y_915_, lean_object* v___y_916_, lean_object* v___y_917_, lean_object* v___y_918_, lean_object* v___y_919_, lean_object* v___y_920_, lean_object* v___y_921_, lean_object* v___y_922_, lean_object* v___y_923_, lean_object* v___y_924_, lean_object* v___y_925_){
_start:
{
lean_object* v_res_926_; 
v_res_926_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_911_, v_init_912_, v_start_913_, v___y_914_, v___y_915_, v___y_916_, v___y_917_, v___y_918_, v___y_919_, v___y_920_, v___y_921_, v___y_922_, v___y_923_, v___y_924_);
lean_dec(v___y_924_);
lean_dec_ref(v___y_923_);
lean_dec(v___y_922_);
lean_dec_ref(v___y_921_);
lean_dec(v___y_920_);
lean_dec_ref(v___y_919_);
lean_dec(v___y_918_);
lean_dec_ref(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v___y_915_);
lean_dec_ref(v___y_914_);
lean_dec(v_start_913_);
return v_res_926_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(lean_object* v_scope_927_, lean_object* v___y_928_, lean_object* v___y_929_, lean_object* v___y_930_, lean_object* v___y_931_, lean_object* v___y_932_, lean_object* v___y_933_, lean_object* v___y_934_, lean_object* v___y_935_, lean_object* v___y_936_, lean_object* v___y_937_, lean_object* v___y_938_){
_start:
{
lean_object* v_lctx_940_; lean_object* v_decls_941_; lean_object* v_nextDeclIdx_942_; lean_object* v_size_943_; uint8_t v___x_944_; 
v_lctx_940_ = lean_ctor_get(v___y_935_, 2);
v_decls_941_ = lean_ctor_get(v_lctx_940_, 1);
v_nextDeclIdx_942_ = lean_ctor_get(v_scope_927_, 3);
v_size_943_ = lean_ctor_get(v_decls_941_, 2);
v___x_944_ = lean_nat_dec_eq(v_nextDeclIdx_942_, v_size_943_);
if (v___x_944_ == 0)
{
lean_object* v___x_945_; 
lean_inc(v_nextDeclIdx_942_);
lean_inc_ref(v_lctx_940_);
v___x_945_ = l_Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0(v_lctx_940_, v_scope_927_, v_nextDeclIdx_942_, v___y_928_, v___y_929_, v___y_930_, v___y_931_, v___y_932_, v___y_933_, v___y_934_, v___y_935_, v___y_936_, v___y_937_, v___y_938_);
lean_dec(v_nextDeclIdx_942_);
if (lean_obj_tag(v___x_945_) == 0)
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_964_; 
v_a_946_ = lean_ctor_get(v___x_945_, 0);
v_isSharedCheck_964_ = !lean_is_exclusive(v___x_945_);
if (v_isSharedCheck_964_ == 0)
{
v___x_948_ = v___x_945_;
v_isShared_949_ = v_isSharedCheck_964_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_945_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_964_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v_specs_950_; lean_object* v_jps_951_; lean_object* v_lastLiftedPre_x3f_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_962_; 
v_specs_950_ = lean_ctor_get(v_a_946_, 0);
v_jps_951_ = lean_ctor_get(v_a_946_, 1);
v_lastLiftedPre_x3f_952_ = lean_ctor_get(v_a_946_, 2);
v_isSharedCheck_962_ = !lean_is_exclusive(v_a_946_);
if (v_isSharedCheck_962_ == 0)
{
lean_object* v_unused_963_; 
v_unused_963_ = lean_ctor_get(v_a_946_, 3);
lean_dec(v_unused_963_);
v___x_954_ = v_a_946_;
v_isShared_955_ = v_isSharedCheck_962_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_lastLiftedPre_x3f_952_);
lean_inc(v_jps_951_);
lean_inc(v_specs_950_);
lean_dec(v_a_946_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_962_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
lean_inc(v_size_943_);
if (v_isShared_955_ == 0)
{
lean_ctor_set(v___x_954_, 3, v_size_943_);
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_961_; 
v_reuseFailAlloc_961_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_961_, 0, v_specs_950_);
lean_ctor_set(v_reuseFailAlloc_961_, 1, v_jps_951_);
lean_ctor_set(v_reuseFailAlloc_961_, 2, v_lastLiftedPre_x3f_952_);
lean_ctor_set(v_reuseFailAlloc_961_, 3, v_size_943_);
v___x_957_ = v_reuseFailAlloc_961_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
lean_object* v___x_959_; 
if (v_isShared_949_ == 0)
{
lean_ctor_set(v___x_948_, 0, v___x_957_);
v___x_959_ = v___x_948_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v___x_957_);
v___x_959_ = v_reuseFailAlloc_960_;
goto v_reusejp_958_;
}
v_reusejp_958_:
{
return v___x_959_;
}
}
}
}
}
else
{
return v___x_945_;
}
}
else
{
lean_object* v___x_965_; 
v___x_965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_965_, 0, v_scope_927_);
return v___x_965_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed(lean_object* v_scope_966_, lean_object* v___y_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_, lean_object* v___y_975_, lean_object* v___y_976_, lean_object* v___y_977_, lean_object* v___y_978_){
_start:
{
lean_object* v_res_979_; 
v_res_979_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0(v_scope_966_, v___y_967_, v___y_968_, v___y_969_, v___y_970_, v___y_971_, v___y_972_, v___y_973_, v___y_974_, v___y_975_, v___y_976_, v___y_977_);
lean_dec(v___y_977_);
lean_dec_ref(v___y_976_);
lean_dec(v___y_975_);
lean_dec_ref(v___y_974_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec(v___y_968_);
lean_dec_ref(v___y_967_);
return v_res_979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(lean_object* v_scope_980_, lean_object* v_goal_981_, lean_object* v_a_982_, lean_object* v_a_983_, lean_object* v_a_984_, lean_object* v_a_985_, lean_object* v_a_986_, lean_object* v_a_987_, lean_object* v_a_988_, lean_object* v_a_989_, lean_object* v_a_990_, lean_object* v_a_991_, lean_object* v_a_992_){
_start:
{
lean_object* v___f_994_; lean_object* v___x_995_; 
v___f_994_ = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___lam__0___boxed), 13, 1);
lean_closure_set(v___f_994_, 0, v_scope_980_);
v___x_995_ = l_Lean_MVarId_withContext___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__1___redArg(v_goal_981_, v___f_994_, v_a_982_, v_a_983_, v_a_984_, v_a_985_, v_a_986_, v_a_987_, v_a_988_, v_a_989_, v_a_990_, v_a_991_, v_a_992_);
return v___x_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs___boxed(lean_object* v_scope_996_, lean_object* v_goal_997_, lean_object* v_a_998_, lean_object* v_a_999_, lean_object* v_a_1000_, lean_object* v_a_1001_, lean_object* v_a_1002_, lean_object* v_a_1003_, lean_object* v_a_1004_, lean_object* v_a_1005_, lean_object* v_a_1006_, lean_object* v_a_1007_, lean_object* v_a_1008_, lean_object* v_a_1009_){
_start:
{
lean_object* v_res_1010_; 
v_res_1010_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs(v_scope_996_, v_goal_997_, v_a_998_, v_a_999_, v_a_1000_, v_a_1001_, v_a_1002_, v_a_1003_, v_a_1004_, v_a_1005_, v_a_1006_, v_a_1007_, v_a_1008_);
lean_dec(v_a_1008_);
lean_dec_ref(v_a_1007_);
lean_dec(v_a_1006_);
lean_dec_ref(v_a_1005_);
lean_dec(v_a_1004_);
lean_dec_ref(v_a_1003_);
lean_dec(v_a_1002_);
lean_dec_ref(v_a_1001_);
lean_dec(v_a_1000_);
lean_dec(v_a_999_);
lean_dec_ref(v_a_998_);
return v_res_1010_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(lean_object* v_as_1011_, size_t v_i_1012_, size_t v_stop_1013_, lean_object* v_b_1014_, lean_object* v___y_1015_, lean_object* v___y_1016_, lean_object* v___y_1017_, lean_object* v___y_1018_, lean_object* v___y_1019_, lean_object* v___y_1020_, lean_object* v___y_1021_, lean_object* v___y_1022_, lean_object* v___y_1023_, lean_object* v___y_1024_, lean_object* v___y_1025_){
_start:
{
lean_object* v___x_1027_; 
v___x_1027_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___redArg(v_as_1011_, v_i_1012_, v_stop_1013_, v_b_1014_, v___y_1022_, v___y_1023_, v___y_1024_, v___y_1025_);
return v___x_1027_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3___boxed(lean_object* v_as_1028_, lean_object* v_i_1029_, lean_object* v_stop_1030_, lean_object* v_b_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_, lean_object* v___y_1034_, lean_object* v___y_1035_, lean_object* v___y_1036_, lean_object* v___y_1037_, lean_object* v___y_1038_, lean_object* v___y_1039_, lean_object* v___y_1040_, lean_object* v___y_1041_, lean_object* v___y_1042_, lean_object* v___y_1043_){
_start:
{
size_t v_i_boxed_1044_; size_t v_stop_boxed_1045_; lean_object* v_res_1046_; 
v_i_boxed_1044_ = lean_unbox_usize(v_i_1029_);
lean_dec(v_i_1029_);
v_stop_boxed_1045_ = lean_unbox_usize(v_stop_1030_);
lean_dec(v_stop_1030_);
v_res_1046_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_PersistentArray_foldlM___at___00Lean_LocalContext_foldlM___at___00Lean_Elab_Tactic_Do_Internal_VCGen_Scope_collectLocalSpecs_spec__0_spec__0_spec__3(v_as_1028_, v_i_boxed_1044_, v_stop_boxed_1045_, v_b_1031_, v___y_1032_, v___y_1033_, v___y_1034_, v___y_1035_, v___y_1036_, v___y_1037_, v___y_1038_, v___y_1039_, v___y_1040_, v___y_1041_, v___y_1042_);
lean_dec(v___y_1042_);
lean_dec_ref(v___y_1041_);
lean_dec(v___y_1040_);
lean_dec_ref(v___y_1039_);
lean_dec(v___y_1038_);
lean_dec_ref(v___y_1037_);
lean_dec(v___y_1036_);
lean_dec_ref(v___y_1035_);
lean_dec(v___y_1034_);
lean_dec(v___y_1033_);
lean_dec_ref(v___y_1032_);
lean_dec_ref(v_as_1028_);
return v_res_1046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(lean_object* v_a_1047_){
_start:
{
lean_object* v___x_1049_; lean_object* v_fuel_1050_; 
v___x_1049_ = lean_st_ref_get(v_a_1047_);
v_fuel_1050_ = lean_ctor_get(v___x_1049_, 6);
lean_inc(v_fuel_1050_);
lean_dec(v___x_1049_);
if (lean_obj_tag(v_fuel_1050_) == 0)
{
lean_object* v_n_1051_; lean_object* v___x_1053_; uint8_t v_isShared_1054_; uint8_t v_isSharedCheck_1061_; 
v_n_1051_ = lean_ctor_get(v_fuel_1050_, 0);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_fuel_1050_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1053_ = v_fuel_1050_;
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
else
{
lean_inc(v_n_1051_);
lean_dec(v_fuel_1050_);
v___x_1053_ = lean_box(0);
v_isShared_1054_ = v_isSharedCheck_1061_;
goto v_resetjp_1052_;
}
v_resetjp_1052_:
{
lean_object* v___x_1055_; uint8_t v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1059_; 
v___x_1055_ = lean_unsigned_to_nat(0u);
v___x_1056_ = lean_nat_dec_eq(v_n_1051_, v___x_1055_);
lean_dec(v_n_1051_);
v___x_1057_ = lean_box(v___x_1056_);
if (v_isShared_1054_ == 0)
{
lean_ctor_set(v___x_1053_, 0, v___x_1057_);
v___x_1059_ = v___x_1053_;
goto v_reusejp_1058_;
}
else
{
lean_object* v_reuseFailAlloc_1060_; 
v_reuseFailAlloc_1060_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1060_, 0, v___x_1057_);
v___x_1059_ = v_reuseFailAlloc_1060_;
goto v_reusejp_1058_;
}
v_reusejp_1058_:
{
return v___x_1059_;
}
}
}
else
{
uint8_t v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec(v_fuel_1050_);
v___x_1062_ = 0;
v___x_1063_ = lean_box(v___x_1062_);
v___x_1064_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1064_, 0, v___x_1063_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg___boxed(lean_object* v_a_1065_, lean_object* v_a_1066_){
_start:
{
lean_object* v_res_1067_; 
v_res_1067_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_1065_);
lean_dec(v_a_1065_);
return v_res_1067_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(lean_object* v_a_1068_, lean_object* v_a_1069_, lean_object* v_a_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_, lean_object* v_a_1075_, lean_object* v_a_1076_, lean_object* v_a_1077_, lean_object* v_a_1078_){
_start:
{
lean_object* v___x_1080_; 
v___x_1080_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___redArg(v_a_1069_);
return v___x_1080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel___boxed(lean_object* v_a_1081_, lean_object* v_a_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_, lean_object* v_a_1085_, lean_object* v_a_1086_, lean_object* v_a_1087_, lean_object* v_a_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_, lean_object* v_a_1091_, lean_object* v_a_1092_){
_start:
{
lean_object* v_res_1093_; 
v_res_1093_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_outOfFuel(v_a_1081_, v_a_1082_, v_a_1083_, v_a_1084_, v_a_1085_, v_a_1086_, v_a_1087_, v_a_1088_, v_a_1089_, v_a_1090_, v_a_1091_);
lean_dec(v_a_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_a_1089_);
lean_dec_ref(v_a_1088_);
lean_dec(v_a_1087_);
lean_dec_ref(v_a_1086_);
lean_dec(v_a_1085_);
lean_dec_ref(v_a_1084_);
lean_dec(v_a_1083_);
lean_dec(v_a_1082_);
lean_dec_ref(v_a_1081_);
return v_res_1093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(lean_object* v_a_1094_){
_start:
{
lean_object* v___x_1096_; lean_object* v_specBackwardRuleCache_1097_; lean_object* v_splitBackwardRuleCache_1098_; lean_object* v_latticeBackwardRuleCache_1099_; lean_object* v_invariants_1100_; lean_object* v_vcs_1101_; lean_object* v_simpState_1102_; lean_object* v_fuel_1103_; lean_object* v_inlineHandledInvariants_1104_; lean_object* v___x_1106_; uint8_t v_isShared_1107_; uint8_t v_isSharedCheck_1129_; 
v___x_1096_ = lean_st_ref_take(v_a_1094_);
v_specBackwardRuleCache_1097_ = lean_ctor_get(v___x_1096_, 0);
v_splitBackwardRuleCache_1098_ = lean_ctor_get(v___x_1096_, 1);
v_latticeBackwardRuleCache_1099_ = lean_ctor_get(v___x_1096_, 2);
v_invariants_1100_ = lean_ctor_get(v___x_1096_, 3);
v_vcs_1101_ = lean_ctor_get(v___x_1096_, 4);
v_simpState_1102_ = lean_ctor_get(v___x_1096_, 5);
v_fuel_1103_ = lean_ctor_get(v___x_1096_, 6);
v_inlineHandledInvariants_1104_ = lean_ctor_get(v___x_1096_, 7);
v_isSharedCheck_1129_ = !lean_is_exclusive(v___x_1096_);
if (v_isSharedCheck_1129_ == 0)
{
v___x_1106_ = v___x_1096_;
v_isShared_1107_ = v_isSharedCheck_1129_;
goto v_resetjp_1105_;
}
else
{
lean_inc(v_inlineHandledInvariants_1104_);
lean_inc(v_fuel_1103_);
lean_inc(v_simpState_1102_);
lean_inc(v_vcs_1101_);
lean_inc(v_invariants_1100_);
lean_inc(v_latticeBackwardRuleCache_1099_);
lean_inc(v_splitBackwardRuleCache_1098_);
lean_inc(v_specBackwardRuleCache_1097_);
lean_dec(v___x_1096_);
v___x_1106_ = lean_box(0);
v_isShared_1107_ = v_isSharedCheck_1129_;
goto v_resetjp_1105_;
}
v_resetjp_1105_:
{
lean_object* v___x_1108_; lean_object* v___y_1110_; 
v___x_1108_ = lean_box(0);
if (lean_obj_tag(v_fuel_1103_) == 0)
{
lean_object* v_n_1116_; lean_object* v_zero_1117_; uint8_t v_isZero_1118_; 
v_n_1116_ = lean_ctor_get(v_fuel_1103_, 0);
v_zero_1117_ = lean_unsigned_to_nat(0u);
v_isZero_1118_ = lean_nat_dec_eq(v_n_1116_, v_zero_1117_);
if (v_isZero_1118_ == 0)
{
lean_object* v___x_1120_; uint8_t v_isShared_1121_; uint8_t v_isSharedCheck_1127_; 
lean_inc(v_n_1116_);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_fuel_1103_);
if (v_isSharedCheck_1127_ == 0)
{
lean_object* v_unused_1128_; 
v_unused_1128_ = lean_ctor_get(v_fuel_1103_, 0);
lean_dec(v_unused_1128_);
v___x_1120_ = v_fuel_1103_;
v_isShared_1121_ = v_isSharedCheck_1127_;
goto v_resetjp_1119_;
}
else
{
lean_dec(v_fuel_1103_);
v___x_1120_ = lean_box(0);
v_isShared_1121_ = v_isSharedCheck_1127_;
goto v_resetjp_1119_;
}
v_resetjp_1119_:
{
lean_object* v_one_1122_; lean_object* v_n_1123_; lean_object* v___x_1125_; 
v_one_1122_ = lean_unsigned_to_nat(1u);
v_n_1123_ = lean_nat_sub(v_n_1116_, v_one_1122_);
lean_dec(v_n_1116_);
if (v_isShared_1121_ == 0)
{
lean_ctor_set(v___x_1120_, 0, v_n_1123_);
v___x_1125_ = v___x_1120_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_n_1123_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
v___y_1110_ = v___x_1125_;
goto v___jp_1109_;
}
}
}
else
{
v___y_1110_ = v_fuel_1103_;
goto v___jp_1109_;
}
}
else
{
v___y_1110_ = v_fuel_1103_;
goto v___jp_1109_;
}
v___jp_1109_:
{
lean_object* v___x_1112_; 
if (v_isShared_1107_ == 0)
{
lean_ctor_set(v___x_1106_, 6, v___y_1110_);
v___x_1112_ = v___x_1106_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1115_; 
v_reuseFailAlloc_1115_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v_reuseFailAlloc_1115_, 0, v_specBackwardRuleCache_1097_);
lean_ctor_set(v_reuseFailAlloc_1115_, 1, v_splitBackwardRuleCache_1098_);
lean_ctor_set(v_reuseFailAlloc_1115_, 2, v_latticeBackwardRuleCache_1099_);
lean_ctor_set(v_reuseFailAlloc_1115_, 3, v_invariants_1100_);
lean_ctor_set(v_reuseFailAlloc_1115_, 4, v_vcs_1101_);
lean_ctor_set(v_reuseFailAlloc_1115_, 5, v_simpState_1102_);
lean_ctor_set(v_reuseFailAlloc_1115_, 6, v___y_1110_);
lean_ctor_set(v_reuseFailAlloc_1115_, 7, v_inlineHandledInvariants_1104_);
v___x_1112_ = v_reuseFailAlloc_1115_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = lean_st_ref_set(v_a_1094_, v___x_1112_);
v___x_1114_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1108_);
return v___x_1114_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg___boxed(lean_object* v_a_1130_, lean_object* v_a_1131_){
_start:
{
lean_object* v_res_1132_; 
v_res_1132_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_1130_);
lean_dec(v_a_1130_);
return v_res_1132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(lean_object* v_a_1133_, lean_object* v_a_1134_, lean_object* v_a_1135_, lean_object* v_a_1136_, lean_object* v_a_1137_, lean_object* v_a_1138_, lean_object* v_a_1139_, lean_object* v_a_1140_, lean_object* v_a_1141_, lean_object* v_a_1142_, lean_object* v_a_1143_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___redArg(v_a_1134_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne___boxed(lean_object* v_a_1146_, lean_object* v_a_1147_, lean_object* v_a_1148_, lean_object* v_a_1149_, lean_object* v_a_1150_, lean_object* v_a_1151_, lean_object* v_a_1152_, lean_object* v_a_1153_, lean_object* v_a_1154_, lean_object* v_a_1155_, lean_object* v_a_1156_, lean_object* v_a_1157_){
_start:
{
lean_object* v_res_1158_; 
v_res_1158_ = l_Lean_Elab_Tactic_Do_Internal_VCGen_burnOne(v_a_1146_, v_a_1147_, v_a_1148_, v_a_1149_, v_a_1150_, v_a_1151_, v_a_1152_, v_a_1153_, v_a_1154_, v_a_1155_, v_a_1156_);
lean_dec(v_a_1156_);
lean_dec_ref(v_a_1155_);
lean_dec(v_a_1154_);
lean_dec_ref(v_a_1153_);
lean_dec(v_a_1152_);
lean_dec_ref(v_a_1151_);
lean_dec(v_a_1150_);
lean_dec_ref(v_a_1149_);
lean_dec(v_a_1148_);
lean_dec(v_a_1147_);
lean_dec_ref(v_a_1146_);
return v_res_1158_;
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
