// Lean compiler output
// Module: Lean.Compiler.LCNF.ToLCNF
// Imports: public import Lean.Meta.AppBuilder public import Lean.Compiler.CSimpAttr public import Lean.Compiler.ImplementedByAttr public import Lean.Compiler.LCNF.Bind public import Lean.Compiler.NeverExtractAttr import Lean.Meta.CasesInfo import Lean.Meta.WHNF import Lean.Compiler.NoncomputableAttr import Lean.Compiler.LCNF.Util import Init.Data.Format.Macro import Init.Omega import Lean.OriginalConstKind
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
static const lean_string_object l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "lcProof"};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__0_value),LEAN_SCALAR_PTR_LITERAL(85, 55, 63, 87, 134, 86, 31, 102)}};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1_value;
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_jp_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_jp_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_fun_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_fun_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_let_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_let_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_cases_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_cases_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_unreach_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_unreach_elim(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(uint8_t);
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement;
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(uint8_t, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__0;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1;
static lean_once_cell_t l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2;
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPurity___redArg(lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_maxView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_minView___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_instHashableFVarId_hash(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5_spec__8___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3___redArg(lean_object*);
uint8_t l_Lean_instBEqFVarId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(uint8_t, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "_alt"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__0_value),LEAN_SCALAR_PTR_LITERAL(19, 71, 85, 208, 12, 9, 171, 45)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static const lean_array_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_x"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__7_value),LEAN_SCALAR_PTR_LITERAL(181, 1, 28, 251, 11, 9, 217, 106)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "_jp"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__9_value),LEAN_SCALAR_PTR_LITERAL(89, 69, 15, 56, 172, 246, 212, 179)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "`Code.bind` failed, empty `cases` found"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_getPrefix(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseLetDecl___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferParamType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkCasesResultType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5_spec__8(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseFunDecl___redArg(uint8_t, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParam___redArg(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_addFunDecl(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDecl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5;
extern lean_object* l_Lean_Meta_instInhabitedConfigWithKey___private__1;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkLetDecl(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6;
static const lean_array_object l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7_value;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2_spec__4(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_anyExpr;
static lean_once_cell_t l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_replace_expr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_toLCNFType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isMarkedBorrowed(lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkParam(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg___closed__0_value;
lean_object* l_Lean_LocalContext_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toExpr___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Eq"};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0_value;
static const lean_string_object l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ndrec"};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(115, 164, 251, 202, 217, 58, 77, 179)}};
static const lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2 = (const lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2_value;
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
uint8_t l_Lean_isCasesOnLike(lean_object*, lean_object*);
uint8_t l_Lean_isNoConfusion(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_tagWithErrorName(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "dependsOnNoncomputable"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(43, 31, 155, 49, 49, 182, 172, 127)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__2_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__1_value),LEAN_SCALAR_PTR_LITERAL(215, 168, 234, 245, 176, 181, 140, 129)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__3_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__3_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__4_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "` not supported by code generator; consider marking definition as `noncomputable`"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__5_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__5_value)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__6_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "failed to compile definition, consider marking it as 'noncomputable' because it depends on '"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__7_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__8;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "', which is 'noncomputable'"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__9_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__10;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Quot"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "mk"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__12_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lift"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__13_value;
lean_object* l_Lean_Name_toString(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_getImplementedBy_x3f(lean_object*, lean_object*);
extern lean_object* l_Lean_noncomputableExt;
uint8_t l_Lean_isNoncomputable(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getOriginalConstKind_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_BinderInfo_isImplicit(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_instBEqBinderInfo_beq(uint8_t, uint8_t);
uint8_t lean_expr_has_loose_bvar(lean_object*, lean_object*);
lean_object* lean_expr_lower_loose_bvars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__1_value;
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___boxed(lean_object*, lean_object*);
lean_object* l_instMonadEST(lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0;
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__1 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__1_value;
lean_object* l_Lean_Core_instMonadCoreM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Core_instMonadCoreM___lam__1___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__2 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__2_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed, .m_arity = 7, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__3 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__3_value;
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1___boxed, .m_arity = 9, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__4 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__4_value;
lean_object* l_ReaderT_instMonad___redArg(lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* l_instInhabitedForall___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38_spec__41(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38_spec__41___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Lean.MonadEnv"};
static const lean_object* l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__0 = (const lean_object*)&l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__0_value;
static const lean_string_object l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Lean.isCtor\?"};
static const lean_object* l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__1 = (const lean_object*)&l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__1_value;
static const lean_string_object l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "unreachable code has been reached"};
static const lean_object* l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2 = (const lean_object*)&l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2_value;
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__3;
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_AsyncConstantInfo_toConstantInfo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "code generator failed, unsupported occurrence of `"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2;
lean_object* l_Lean_Meta_isConstructorApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_toCtorIfLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__0;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__1 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__1_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__3 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__3_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__14;
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__25___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_instInhabitedMetaM___lam__0___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27___closed__0 = (const lean_object*)&l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27___closed__0_value;
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Compiler.LCNF.ToLCNF"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 81, .m_capacity = 81, .m_length = 80, .m_data = "_private.Lean.Compiler.LCNF.ToLCNF.0.Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCases"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 180, .m_capacity = 180, .m_length = 179, .m_data = "assertion violation: indAppF == typeName\n            -- TODO: We only use `toArray` so that we get access to `findIdx\?`. Remove\n            -- this when that changes.\n            "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3;
lean_object* l_Lean_Expr_getAppFnArgs(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28_spec__43___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__2;
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
size_t lean_usize_mul(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_beta(lean_object*, lean_object*);
lean_object* l_Subarray_copy___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__11_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__13_value),LEAN_SCALAR_PTR_LITERAL(91, 125, 38, 34, 222, 200, 201, 80)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__11_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__12_value),LEAN_SCALAR_PTR_LITERAL(255, 113, 137, 82, 82, 132, 58, 248)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rec"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 17, 7, 2, 233, 148, 36, 75)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__1_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "recOn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__0_value),LEAN_SCALAR_PTR_LITERAL(143, 37, 101, 248, 9, 246, 191, 223)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__2_value),LEAN_SCALAR_PTR_LITERAL(207, 56, 58, 111, 136, 71, 194, 11)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "HEq"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 72, 177, 37, 35, 66, 175, 127)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__1_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(67, 180, 169, 191, 74, 196, 152, 188)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__2_value_aux_0),((lean_object*)&l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__1_value),LEAN_SCALAR_PTR_LITERAL(7, 86, 165, 32, 90, 213, 176, 216)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__2_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "And"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__4_value),LEAN_SCALAR_PTR_LITERAL(49, 220, 212, 156, 122, 214, 55, 135)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(192, 86, 186, 46, 229, 41, 245, 36)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__6_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 106, 229, 132, 85, 98, 57, 253)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "False"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__8_value),LEAN_SCALAR_PTR_LITERAL(227, 122, 176, 177, 50, 175, 152, 12)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(122, 221, 252, 198, 56, 59, 37, 193)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Empty"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__10_value),LEAN_SCALAR_PTR_LITERAL(145, 208, 51, 224, 197, 14, 63, 134)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(224, 106, 251, 72, 254, 34, 118, 241)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11_value;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "lcUnreachable"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__12_value),LEAN_SCALAR_PTR_LITERAL(244, 152, 7, 242, 102, 125, 47, 175)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isPredicateType(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_erasedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_joinTypes(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__1;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__0;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__3;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 53, .m_capacity = 53, .m_length = 52, .m_data = "assertion violation: casesInfo.numAlts == 1\n        "};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__4 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__4_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__5;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__6;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__7;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__8;
lean_object* l_CasesInfo_numAlts(lean_object*);
lean_object* l_List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_instInhabitedCasesAltInfo_default;
lean_object* l_Lean_Meta_isInductivePredicateVal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Compiler.LCNF.ToLCNF.0.Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCtor"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__1;
lean_object* l_Lean_Compiler_CSimp_replaceConstant(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_hasNeverExtractAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 82, .m_capacity = 82, .m_length = 81, .m_data = "_private.Lean.Compiler.LCNF.ToLCNF.0.Lean.Compiler.LCNF.ToLCNF.toLCNF.visitProjFn"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__10(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "_private.Lean.Compiler.LCNF.ToLCNF.0.Lean.Compiler.LCNF.ToLCNF.toLCNF.visitAppDefaultConst"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isRuntimeBuiltinType(lean_object*);
lean_object* l_Lean_Core_instantiateValueLevelParams(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__12(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 87, .m_capacity = 87, .m_length = 86, .m_data = "_private.Lean.Compiler.LCNF.ToLCNF.0.Lean.Compiler.LCNF.ToLCNF.toLCNF.visitNoConfusion"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1;
lean_object* l_Lean_getNoConfusionInfo(lean_object*, lean_object*);
lean_object* l_Lean_NoConfusionInfo_arity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0___boxed, .m_arity = 8, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 84, .m_capacity = 84, .m_length = 83, .m_data = "_private.Lean.Compiler.LCNF.ToLCNF.0.Lean.Compiler.LCNF.ToLCNF.toLCNF.visitQuotLift"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1;
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "lcInv"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__11_value),LEAN_SCALAR_PTR_LITERAL(91, 127, 250, 116, 111, 99, 160, 200)}};
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3_value_aux_0),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(246, 129, 23, 78, 51, 209, 87, 155)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__13(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_getCasesInfo_x3f(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getCtorArity_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_f"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(253, 65, 185, 154, 193, 83, 240, 170)}};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1_value;
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLambda(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_getStructureInfo(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkProjection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 80, .m_capacity = 80, .m_length = 79, .m_data = "_private.Lean.Compiler.LCNF.ToLCNF.0.Lean.Compiler.LCNF.ToLCNF.toLCNF.visitCore"};
static const lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0 = (const lean_object*)&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0_value;
static lean_once_cell_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__25(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29(size_t, size_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28_spec__43(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_isLCProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1));
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Expr_isAppOfArity(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_isLCProof___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
lean_dec_ref(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_isLCProof___closed__1));
x_3 = l_Lean_mkConst(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0, &l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0_once, _init_l_Lean_Compiler_LCNF_ToLCNF_mkLcProof___closed__0);
x_3 = l_Lean_Expr_app___override(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorIdx(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
default: 
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorIdx___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorIdx(x_1);
lean_dec_ref(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_2(x_2, x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_6);
lean_dec_ref(x_1);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_jp_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_jp_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_fun_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_fun_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_let_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_let_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_cases_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_cases_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_unreach_elim___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_Element_unreach_elim(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_ToLCNF_Element_ctorElim___redArg(x_2, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__0(void) {
_start:
{
uint8_t x_1; lean_object* x_2; 
x_1 = 0;
x_2 = l_Lean_Compiler_LCNF_instInhabitedFunDecl_default__1(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__0, &l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__0_once, _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__1, &l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__1_once, _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default___closed__1);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = 0;
x_5 = l_Lean_Compiler_LCNF_findFunDecl_x3f___redArg(x_4, x_1, x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 1)
{
lean_dec_ref(x_6);
lean_dec(x_1);
return x_5;
}
else
{
lean_object* x_7; 
lean_dec_ref(x_5);
lean_dec(x_6);
x_7 = l_Lean_Compiler_LCNF_findLetValue_x3f___redArg(x_4, x_1, x_2);
lean_dec(x_1);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_24; 
x_8 = lean_ctor_get(x_7, 0);
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
x_9 = x_7;
x_10 = x_24;
goto block_23;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_24;
goto block_23;
}
block_23:
{
if (lean_obj_tag(x_8) == 1)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec_ref(x_8);
if (lean_obj_tag(x_16) == 4)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc_ref(x_18);
lean_dec_ref(x_16);
x_19 = lean_array_get_size(x_18);
lean_dec_ref(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_dec(x_17);
goto block_15;
}
else
{
lean_del_object(x_9);
x_1 = x_17;
goto _start;
}
}
else
{
lean_dec(x_16);
goto block_15;
}
}
else
{
lean_dec(x_8);
goto block_15;
}
block_15:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
if (x_10 == 0)
{
lean_ctor_set(x_9, 0, x_11);
x_12 = x_9;
goto block_13;
}
else
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_11);
x_12 = x_14;
goto block_13;
}
block_13:
{
return x_12;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
x_25 = lean_ctor_get(x_7, 0);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
x_26 = x_7;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
}
else
{
lean_dec(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__0, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__0_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_st_ref_get(x_5);
x_10 = lean_st_ref_get(x_3);
x_11 = l_Lean_Compiler_LCNF_getPurity___redArg(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_34; 
x_12 = lean_ctor_get(x_11, 0);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
x_13 = x_11;
x_14 = x_34;
goto block_33;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_31; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_10, 0);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_10, 1);
lean_dec(x_32);
x_17 = x_10;
x_18 = x_31;
goto block_30;
}
else
{
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_31;
goto block_30;
}
block_30:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unbox(x_12);
lean_dec(x_12);
x_20 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16, x_19);
lean_dec_ref(x_16);
x_21 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2);
lean_inc_ref(x_7);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_7);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 0, x_22);
x_23 = x_17;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_1);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_24);
x_25 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_11, 0);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
x_36 = x_11;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg(x_2, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_660; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
x_6 = lean_ctor_get(x_2, 4);
x_660 = !lean_is_exclusive(x_2);
if (x_660 == 0)
{
lean_object* x_661; 
x_661 = lean_ctor_get(x_2, 0);
lean_dec(x_661);
x_7 = x_2;
x_8 = x_660;
goto block_659;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_7 = lean_box(0);
x_8 = x_660;
goto block_659;
}
block_659:
{
uint8_t x_9; 
x_9 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_9) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_1, x_5);
x_11 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_10) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_ctor_get(x_6, 1);
x_15 = lean_ctor_get(x_6, 2);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
x_17 = lean_ctor_get(x_6, 4);
x_18 = lean_unsigned_to_nat(3u);
x_19 = lean_nat_mul(x_18, x_12);
x_20 = lean_nat_dec_lt(x_19, x_13);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_16);
x_21 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_22 = lean_nat_add(x_21, x_13);
lean_dec(x_21);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_22);
x_23 = x_7;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_4);
lean_ctor_set(x_25, 3, x_10);
lean_ctor_set(x_25, 4, x_6);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
else
{
lean_object* x_26; uint8_t x_27; uint8_t x_89; 
lean_inc(x_17);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
x_89 = !lean_is_exclusive(x_6);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_6, 4);
lean_dec(x_90);
x_91 = lean_ctor_get(x_6, 3);
lean_dec(x_91);
x_92 = lean_ctor_get(x_6, 2);
lean_dec(x_92);
x_93 = lean_ctor_get(x_6, 1);
lean_dec(x_93);
x_94 = lean_ctor_get(x_6, 0);
lean_dec(x_94);
x_26 = x_6;
x_27 = x_89;
goto block_88;
}
else
{
lean_dec(x_6);
x_26 = lean_box(0);
x_27 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
x_30 = lean_ctor_get(x_16, 2);
x_31 = lean_ctor_get(x_16, 3);
x_32 = lean_ctor_get(x_16, 4);
x_33 = lean_ctor_get(x_17, 0);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_mul(x_34, x_33);
x_36 = lean_nat_dec_lt(x_28, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; uint8_t x_64; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_65 = lean_ctor_get(x_16, 4);
lean_dec(x_65);
x_66 = lean_ctor_get(x_16, 3);
lean_dec(x_66);
x_67 = lean_ctor_get(x_16, 2);
lean_dec(x_67);
x_68 = lean_ctor_get(x_16, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_16, 0);
lean_dec(x_69);
x_37 = x_16;
x_38 = x_64;
goto block_63;
}
else
{
lean_dec(x_16);
x_37 = lean_box(0);
x_38 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; 
x_39 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_40 = lean_nat_add(x_39, x_13);
lean_dec(x_13);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_31, 0);
lean_inc(x_61);
x_52 = x_61;
goto block_60;
}
else
{
lean_object* x_62; 
x_62 = lean_unsigned_to_nat(0u);
x_52 = x_62;
goto block_60;
}
block_51:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_38 == 0)
{
lean_ctor_set(x_37, 4, x_17);
lean_ctor_set(x_37, 3, x_32);
lean_ctor_set(x_37, 2, x_15);
lean_ctor_set(x_37, 1, x_14);
lean_ctor_set(x_37, 0, x_44);
x_45 = x_37;
goto block_49;
}
else
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_14);
lean_ctor_set(x_50, 2, x_15);
lean_ctor_set(x_50, 3, x_32);
lean_ctor_set(x_50, 4, x_17);
x_45 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_46; 
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_45);
lean_ctor_set(x_26, 3, x_41);
lean_ctor_set(x_26, 2, x_30);
lean_ctor_set(x_26, 1, x_29);
lean_ctor_set(x_26, 0, x_40);
x_46 = x_26;
goto block_47;
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_29);
lean_ctor_set(x_48, 2, x_30);
lean_ctor_set(x_48, 3, x_41);
lean_ctor_set(x_48, 4, x_45);
x_46 = x_48;
goto block_47;
}
block_47:
{
return x_46;
}
}
}
block_60:
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_nat_add(x_39, x_52);
lean_dec(x_52);
lean_dec(x_39);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_31);
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_53);
x_54 = x_7;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_59, 0, x_53);
lean_ctor_set(x_59, 1, x_3);
lean_ctor_set(x_59, 2, x_4);
lean_ctor_set(x_59, 3, x_10);
lean_ctor_set(x_59, 4, x_31);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
x_55 = lean_nat_add(x_11, x_33);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_32, 0);
lean_inc(x_56);
x_41 = x_54;
x_42 = x_55;
x_43 = x_56;
goto block_51;
}
else
{
lean_object* x_57; 
x_57 = lean_unsigned_to_nat(0u);
x_41 = x_54;
x_42 = x_55;
x_43 = x_57;
goto block_51;
}
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_del_object(x_7);
x_70 = lean_nat_add(x_11, x_12);
lean_dec(x_12);
x_71 = lean_nat_add(x_70, x_13);
lean_dec(x_13);
x_72 = lean_nat_add(x_70, x_28);
lean_dec(x_70);
lean_inc_ref(x_10);
if (x_27 == 0)
{
lean_ctor_set(x_26, 4, x_16);
lean_ctor_set(x_26, 3, x_10);
lean_ctor_set(x_26, 2, x_4);
lean_ctor_set(x_26, 1, x_3);
lean_ctor_set(x_26, 0, x_72);
x_73 = x_26;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_3);
lean_ctor_set(x_87, 2, x_4);
lean_ctor_set(x_87, 3, x_10);
lean_ctor_set(x_87, 4, x_16);
x_73 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_74; uint8_t x_75; uint8_t x_80; 
x_80 = !lean_is_exclusive(x_10);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_81 = lean_ctor_get(x_10, 4);
lean_dec(x_81);
x_82 = lean_ctor_get(x_10, 3);
lean_dec(x_82);
x_83 = lean_ctor_get(x_10, 2);
lean_dec(x_83);
x_84 = lean_ctor_get(x_10, 1);
lean_dec(x_84);
x_85 = lean_ctor_get(x_10, 0);
lean_dec(x_85);
x_74 = x_10;
x_75 = x_80;
goto block_79;
}
else
{
lean_dec(x_10);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
lean_ctor_set(x_74, 4, x_17);
lean_ctor_set(x_74, 3, x_73);
lean_ctor_set(x_74, 2, x_15);
lean_ctor_set(x_74, 1, x_14);
lean_ctor_set(x_74, 0, x_71);
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_14);
lean_ctor_set(x_78, 2, x_15);
lean_ctor_set(x_78, 3, x_73);
lean_ctor_set(x_78, 4, x_17);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_10, 0);
lean_inc(x_95);
x_96 = lean_nat_add(x_11, x_95);
lean_dec(x_95);
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_10);
lean_ctor_set(x_7, 0, x_96);
x_97 = x_7;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_3);
lean_ctor_set(x_99, 2, x_4);
lean_ctor_set(x_99, 3, x_10);
lean_ctor_set(x_99, 4, x_6);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_100; 
x_100 = lean_ctor_get(x_6, 3);
lean_inc(x_100);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_6, 4);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; uint8_t x_117; 
x_102 = lean_ctor_get(x_6, 0);
x_103 = lean_ctor_get(x_6, 1);
x_104 = lean_ctor_get(x_6, 2);
x_117 = !lean_is_exclusive(x_6);
if (x_117 == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_6, 4);
lean_dec(x_118);
x_119 = lean_ctor_get(x_6, 3);
lean_dec(x_119);
x_105 = x_6;
x_106 = x_117;
goto block_116;
}
else
{
lean_inc(x_104);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_6);
x_105 = lean_box(0);
x_106 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_107 = lean_ctor_get(x_100, 0);
x_108 = lean_nat_add(x_11, x_102);
lean_dec(x_102);
x_109 = lean_nat_add(x_11, x_107);
if (x_106 == 0)
{
lean_ctor_set(x_105, 4, x_100);
lean_ctor_set(x_105, 3, x_10);
lean_ctor_set(x_105, 2, x_4);
lean_ctor_set(x_105, 1, x_3);
lean_ctor_set(x_105, 0, x_109);
x_110 = x_105;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_115, 0, x_109);
lean_ctor_set(x_115, 1, x_3);
lean_ctor_set(x_115, 2, x_4);
lean_ctor_set(x_115, 3, x_10);
lean_ctor_set(x_115, 4, x_100);
x_110 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_111; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_101);
lean_ctor_set(x_7, 3, x_110);
lean_ctor_set(x_7, 2, x_104);
lean_ctor_set(x_7, 1, x_103);
lean_ctor_set(x_7, 0, x_108);
x_111 = x_7;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_113, 0, x_108);
lean_ctor_set(x_113, 1, x_103);
lean_ctor_set(x_113, 2, x_104);
lean_ctor_set(x_113, 3, x_110);
lean_ctor_set(x_113, 4, x_101);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_144; 
x_120 = lean_ctor_get(x_6, 1);
x_121 = lean_ctor_get(x_6, 2);
x_144 = !lean_is_exclusive(x_6);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_6, 4);
lean_dec(x_145);
x_146 = lean_ctor_get(x_6, 3);
lean_dec(x_146);
x_147 = lean_ctor_get(x_6, 0);
lean_dec(x_147);
x_122 = x_6;
x_123 = x_144;
goto block_143;
}
else
{
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_6);
x_122 = lean_box(0);
x_123 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; uint8_t x_139; 
x_124 = lean_ctor_get(x_100, 1);
x_125 = lean_ctor_get(x_100, 2);
x_139 = !lean_is_exclusive(x_100);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_100, 4);
lean_dec(x_140);
x_141 = lean_ctor_get(x_100, 3);
lean_dec(x_141);
x_142 = lean_ctor_get(x_100, 0);
lean_dec(x_142);
x_126 = x_100;
x_127 = x_139;
goto block_138;
}
else
{
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_100);
x_126 = lean_box(0);
x_127 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_unsigned_to_nat(3u);
if (x_127 == 0)
{
lean_ctor_set(x_126, 4, x_101);
lean_ctor_set(x_126, 3, x_101);
lean_ctor_set(x_126, 2, x_4);
lean_ctor_set(x_126, 1, x_3);
lean_ctor_set(x_126, 0, x_11);
x_129 = x_126;
goto block_136;
}
else
{
lean_object* x_137; 
x_137 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_137, 0, x_11);
lean_ctor_set(x_137, 1, x_3);
lean_ctor_set(x_137, 2, x_4);
lean_ctor_set(x_137, 3, x_101);
lean_ctor_set(x_137, 4, x_101);
x_129 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_130; 
if (x_123 == 0)
{
lean_ctor_set(x_122, 3, x_101);
lean_ctor_set(x_122, 0, x_11);
x_130 = x_122;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_135, 0, x_11);
lean_ctor_set(x_135, 1, x_120);
lean_ctor_set(x_135, 2, x_121);
lean_ctor_set(x_135, 3, x_101);
lean_ctor_set(x_135, 4, x_101);
x_130 = x_135;
goto block_134;
}
block_134:
{
lean_object* x_131; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_130);
lean_ctor_set(x_7, 3, x_129);
lean_ctor_set(x_7, 2, x_125);
lean_ctor_set(x_7, 1, x_124);
lean_ctor_set(x_7, 0, x_128);
x_131 = x_7;
goto block_132;
}
else
{
lean_object* x_133; 
x_133 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_133, 0, x_128);
lean_ctor_set(x_133, 1, x_124);
lean_ctor_set(x_133, 2, x_125);
lean_ctor_set(x_133, 3, x_129);
lean_ctor_set(x_133, 4, x_130);
x_131 = x_133;
goto block_132;
}
block_132:
{
return x_131;
}
}
}
}
}
}
}
else
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_6, 4);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; uint8_t x_161; 
x_149 = lean_ctor_get(x_6, 1);
x_150 = lean_ctor_get(x_6, 2);
x_161 = !lean_is_exclusive(x_6);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_6, 4);
lean_dec(x_162);
x_163 = lean_ctor_get(x_6, 3);
lean_dec(x_163);
x_164 = lean_ctor_get(x_6, 0);
lean_dec(x_164);
x_151 = x_6;
x_152 = x_161;
goto block_160;
}
else
{
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_6);
x_151 = lean_box(0);
x_152 = x_161;
goto block_160;
}
block_160:
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_unsigned_to_nat(3u);
if (x_152 == 0)
{
lean_ctor_set(x_151, 4, x_100);
lean_ctor_set(x_151, 2, x_4);
lean_ctor_set(x_151, 1, x_3);
lean_ctor_set(x_151, 0, x_11);
x_154 = x_151;
goto block_158;
}
else
{
lean_object* x_159; 
x_159 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_159, 0, x_11);
lean_ctor_set(x_159, 1, x_3);
lean_ctor_set(x_159, 2, x_4);
lean_ctor_set(x_159, 3, x_100);
lean_ctor_set(x_159, 4, x_100);
x_154 = x_159;
goto block_158;
}
block_158:
{
lean_object* x_155; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_148);
lean_ctor_set(x_7, 3, x_154);
lean_ctor_set(x_7, 2, x_150);
lean_ctor_set(x_7, 1, x_149);
lean_ctor_set(x_7, 0, x_153);
x_155 = x_7;
goto block_156;
}
else
{
lean_object* x_157; 
x_157 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_157, 0, x_153);
lean_ctor_set(x_157, 1, x_149);
lean_ctor_set(x_157, 2, x_150);
lean_ctor_set(x_157, 3, x_154);
lean_ctor_set(x_157, 4, x_148);
x_155 = x_157;
goto block_156;
}
block_156:
{
return x_155;
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_178; 
x_165 = lean_ctor_get(x_6, 0);
x_166 = lean_ctor_get(x_6, 1);
x_167 = lean_ctor_get(x_6, 2);
x_178 = !lean_is_exclusive(x_6);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_6, 4);
lean_dec(x_179);
x_180 = lean_ctor_get(x_6, 3);
lean_dec(x_180);
x_168 = x_6;
x_169 = x_178;
goto block_177;
}
else
{
lean_inc(x_167);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_6);
x_168 = lean_box(0);
x_169 = x_178;
goto block_177;
}
block_177:
{
lean_object* x_170; 
if (x_169 == 0)
{
lean_ctor_set(x_168, 3, x_148);
x_170 = x_168;
goto block_175;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_176, 0, x_165);
lean_ctor_set(x_176, 1, x_166);
lean_ctor_set(x_176, 2, x_167);
lean_ctor_set(x_176, 3, x_148);
lean_ctor_set(x_176, 4, x_148);
x_170 = x_176;
goto block_175;
}
block_175:
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_170);
lean_ctor_set(x_7, 3, x_148);
lean_ctor_set(x_7, 0, x_171);
x_172 = x_7;
goto block_173;
}
else
{
lean_object* x_174; 
x_174 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_3);
lean_ctor_set(x_174, 2, x_4);
lean_ctor_set(x_174, 3, x_148);
lean_ctor_set(x_174, 4, x_170);
x_172 = x_174;
goto block_173;
}
block_173:
{
return x_172;
}
}
}
}
}
}
else
{
lean_object* x_181; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 3, x_6);
lean_ctor_set(x_7, 0, x_11);
x_181 = x_7;
goto block_182;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_183, 0, x_11);
lean_ctor_set(x_183, 1, x_3);
lean_ctor_set(x_183, 2, x_4);
lean_ctor_set(x_183, 3, x_6);
lean_ctor_set(x_183, 4, x_6);
x_181 = x_183;
goto block_182;
}
block_182:
{
return x_181;
}
}
}
}
case 1:
{
lean_del_object(x_7);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_5) == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; 
x_184 = lean_ctor_get(x_5, 0);
x_185 = lean_ctor_get(x_5, 1);
x_186 = lean_ctor_get(x_5, 2);
x_187 = lean_ctor_get(x_5, 3);
x_188 = lean_ctor_get(x_5, 4);
lean_inc(x_188);
x_189 = lean_ctor_get(x_6, 0);
x_190 = lean_ctor_get(x_6, 1);
x_191 = lean_ctor_get(x_6, 2);
x_192 = lean_ctor_get(x_6, 3);
lean_inc(x_192);
x_193 = lean_ctor_get(x_6, 4);
x_194 = lean_unsigned_to_nat(1u);
x_195 = lean_nat_dec_lt(x_184, x_189);
if (x_195 == 0)
{
lean_object* x_196; uint8_t x_197; uint8_t x_331; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_331 = !lean_is_exclusive(x_5);
if (x_331 == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_332 = lean_ctor_get(x_5, 4);
lean_dec(x_332);
x_333 = lean_ctor_get(x_5, 3);
lean_dec(x_333);
x_334 = lean_ctor_get(x_5, 2);
lean_dec(x_334);
x_335 = lean_ctor_get(x_5, 1);
lean_dec(x_335);
x_336 = lean_ctor_get(x_5, 0);
lean_dec(x_336);
x_196 = x_5;
x_197 = x_331;
goto block_330;
}
else
{
lean_dec(x_5);
x_196 = lean_box(0);
x_197 = x_331;
goto block_330;
}
block_330:
{
lean_object* x_198; lean_object* x_199; 
x_198 = l_Std_DTreeMap_Internal_Impl_maxView___redArg(x_185, x_186, x_187, x_188);
x_199 = lean_ctor_get(x_198, 2);
lean_inc(x_199);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; 
x_200 = lean_ctor_get(x_198, 0);
lean_inc(x_200);
x_201 = lean_ctor_get(x_198, 1);
lean_inc(x_201);
lean_dec_ref(x_198);
x_202 = lean_ctor_get(x_199, 0);
x_203 = lean_unsigned_to_nat(3u);
x_204 = lean_nat_mul(x_203, x_202);
x_205 = lean_nat_dec_lt(x_204, x_189);
lean_dec(x_204);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_192);
x_206 = lean_nat_add(x_194, x_202);
x_207 = lean_nat_add(x_206, x_189);
lean_dec(x_206);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_6);
lean_ctor_set(x_196, 3, x_199);
lean_ctor_set(x_196, 2, x_201);
lean_ctor_set(x_196, 1, x_200);
lean_ctor_set(x_196, 0, x_207);
x_208 = x_196;
goto block_209;
}
else
{
lean_object* x_210; 
x_210 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_200);
lean_ctor_set(x_210, 2, x_201);
lean_ctor_set(x_210, 3, x_199);
lean_ctor_set(x_210, 4, x_6);
x_208 = x_210;
goto block_209;
}
block_209:
{
return x_208;
}
}
else
{
lean_object* x_211; uint8_t x_212; uint8_t x_265; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_265 = !lean_is_exclusive(x_6);
if (x_265 == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_266 = lean_ctor_get(x_6, 4);
lean_dec(x_266);
x_267 = lean_ctor_get(x_6, 3);
lean_dec(x_267);
x_268 = lean_ctor_get(x_6, 2);
lean_dec(x_268);
x_269 = lean_ctor_get(x_6, 1);
lean_dec(x_269);
x_270 = lean_ctor_get(x_6, 0);
lean_dec(x_270);
x_211 = x_6;
x_212 = x_265;
goto block_264;
}
else
{
lean_dec(x_6);
x_211 = lean_box(0);
x_212 = x_265;
goto block_264;
}
block_264:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
x_213 = lean_ctor_get(x_192, 0);
x_214 = lean_ctor_get(x_192, 1);
x_215 = lean_ctor_get(x_192, 2);
x_216 = lean_ctor_get(x_192, 3);
x_217 = lean_ctor_get(x_192, 4);
x_218 = lean_ctor_get(x_193, 0);
x_219 = lean_unsigned_to_nat(2u);
x_220 = lean_nat_mul(x_219, x_218);
x_221 = lean_nat_dec_lt(x_213, x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; uint8_t x_223; uint8_t x_249; 
lean_inc(x_217);
lean_inc(x_216);
lean_inc(x_215);
lean_inc(x_214);
x_249 = !lean_is_exclusive(x_192);
if (x_249 == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_250 = lean_ctor_get(x_192, 4);
lean_dec(x_250);
x_251 = lean_ctor_get(x_192, 3);
lean_dec(x_251);
x_252 = lean_ctor_get(x_192, 2);
lean_dec(x_252);
x_253 = lean_ctor_get(x_192, 1);
lean_dec(x_253);
x_254 = lean_ctor_get(x_192, 0);
lean_dec(x_254);
x_222 = x_192;
x_223 = x_249;
goto block_248;
}
else
{
lean_dec(x_192);
x_222 = lean_box(0);
x_223 = x_249;
goto block_248;
}
block_248:
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_237; 
x_224 = lean_nat_add(x_194, x_202);
x_225 = lean_nat_add(x_224, x_189);
lean_dec(x_189);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_246; 
x_246 = lean_ctor_get(x_216, 0);
lean_inc(x_246);
x_237 = x_246;
goto block_245;
}
else
{
lean_object* x_247; 
x_247 = lean_unsigned_to_nat(0u);
x_237 = x_247;
goto block_245;
}
block_236:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_nat_add(x_227, x_228);
lean_dec(x_228);
lean_dec(x_227);
if (x_223 == 0)
{
lean_ctor_set(x_222, 4, x_193);
lean_ctor_set(x_222, 3, x_217);
lean_ctor_set(x_222, 2, x_191);
lean_ctor_set(x_222, 1, x_190);
lean_ctor_set(x_222, 0, x_229);
x_230 = x_222;
goto block_234;
}
else
{
lean_object* x_235; 
x_235 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_235, 0, x_229);
lean_ctor_set(x_235, 1, x_190);
lean_ctor_set(x_235, 2, x_191);
lean_ctor_set(x_235, 3, x_217);
lean_ctor_set(x_235, 4, x_193);
x_230 = x_235;
goto block_234;
}
block_234:
{
lean_object* x_231; 
if (x_212 == 0)
{
lean_ctor_set(x_211, 4, x_230);
lean_ctor_set(x_211, 3, x_226);
lean_ctor_set(x_211, 2, x_215);
lean_ctor_set(x_211, 1, x_214);
lean_ctor_set(x_211, 0, x_225);
x_231 = x_211;
goto block_232;
}
else
{
lean_object* x_233; 
x_233 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_233, 0, x_225);
lean_ctor_set(x_233, 1, x_214);
lean_ctor_set(x_233, 2, x_215);
lean_ctor_set(x_233, 3, x_226);
lean_ctor_set(x_233, 4, x_230);
x_231 = x_233;
goto block_232;
}
block_232:
{
return x_231;
}
}
}
block_245:
{
lean_object* x_238; lean_object* x_239; 
x_238 = lean_nat_add(x_224, x_237);
lean_dec(x_237);
lean_dec(x_224);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_216);
lean_ctor_set(x_196, 3, x_199);
lean_ctor_set(x_196, 2, x_201);
lean_ctor_set(x_196, 1, x_200);
lean_ctor_set(x_196, 0, x_238);
x_239 = x_196;
goto block_243;
}
else
{
lean_object* x_244; 
x_244 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_244, 0, x_238);
lean_ctor_set(x_244, 1, x_200);
lean_ctor_set(x_244, 2, x_201);
lean_ctor_set(x_244, 3, x_199);
lean_ctor_set(x_244, 4, x_216);
x_239 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_240; 
x_240 = lean_nat_add(x_194, x_218);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_241; 
x_241 = lean_ctor_get(x_217, 0);
lean_inc(x_241);
x_226 = x_239;
x_227 = x_240;
x_228 = x_241;
goto block_236;
}
else
{
lean_object* x_242; 
x_242 = lean_unsigned_to_nat(0u);
x_226 = x_239;
x_227 = x_240;
x_228 = x_242;
goto block_236;
}
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_nat_add(x_194, x_202);
x_256 = lean_nat_add(x_255, x_189);
lean_dec(x_189);
x_257 = lean_nat_add(x_255, x_213);
lean_dec(x_255);
if (x_212 == 0)
{
lean_ctor_set(x_211, 4, x_192);
lean_ctor_set(x_211, 3, x_199);
lean_ctor_set(x_211, 2, x_201);
lean_ctor_set(x_211, 1, x_200);
lean_ctor_set(x_211, 0, x_257);
x_258 = x_211;
goto block_262;
}
else
{
lean_object* x_263; 
x_263 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_263, 0, x_257);
lean_ctor_set(x_263, 1, x_200);
lean_ctor_set(x_263, 2, x_201);
lean_ctor_set(x_263, 3, x_199);
lean_ctor_set(x_263, 4, x_192);
x_258 = x_263;
goto block_262;
}
block_262:
{
lean_object* x_259; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_258);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_256);
x_259 = x_196;
goto block_260;
}
else
{
lean_object* x_261; 
x_261 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_261, 0, x_256);
lean_ctor_set(x_261, 1, x_190);
lean_ctor_set(x_261, 2, x_191);
lean_ctor_set(x_261, 3, x_258);
lean_ctor_set(x_261, 4, x_193);
x_259 = x_261;
goto block_260;
}
block_260:
{
return x_259;
}
}
}
}
}
}
else
{
lean_object* x_271; uint8_t x_272; uint8_t x_324; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
lean_inc(x_189);
x_324 = !lean_is_exclusive(x_6);
if (x_324 == 0)
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_325 = lean_ctor_get(x_6, 4);
lean_dec(x_325);
x_326 = lean_ctor_get(x_6, 3);
lean_dec(x_326);
x_327 = lean_ctor_get(x_6, 2);
lean_dec(x_327);
x_328 = lean_ctor_get(x_6, 1);
lean_dec(x_328);
x_329 = lean_ctor_get(x_6, 0);
lean_dec(x_329);
x_271 = x_6;
x_272 = x_324;
goto block_323;
}
else
{
lean_dec(x_6);
x_271 = lean_box(0);
x_272 = x_324;
goto block_323;
}
block_323:
{
if (lean_obj_tag(x_192) == 0)
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_198, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_198, 1);
lean_inc(x_274);
lean_dec_ref(x_198);
x_275 = lean_ctor_get(x_192, 0);
x_276 = lean_nat_add(x_194, x_189);
lean_dec(x_189);
x_277 = lean_nat_add(x_194, x_275);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_192);
lean_ctor_set(x_271, 3, x_199);
lean_ctor_set(x_271, 2, x_274);
lean_ctor_set(x_271, 1, x_273);
lean_ctor_set(x_271, 0, x_277);
x_278 = x_271;
goto block_282;
}
else
{
lean_object* x_283; 
x_283 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_283, 0, x_277);
lean_ctor_set(x_283, 1, x_273);
lean_ctor_set(x_283, 2, x_274);
lean_ctor_set(x_283, 3, x_199);
lean_ctor_set(x_283, 4, x_192);
x_278 = x_283;
goto block_282;
}
block_282:
{
lean_object* x_279; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_278);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_276);
x_279 = x_196;
goto block_280;
}
else
{
lean_object* x_281; 
x_281 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_281, 0, x_276);
lean_ctor_set(x_281, 1, x_190);
lean_ctor_set(x_281, 2, x_191);
lean_ctor_set(x_281, 3, x_278);
lean_ctor_set(x_281, 4, x_193);
x_279 = x_281;
goto block_280;
}
block_280:
{
return x_279;
}
}
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_301; 
lean_dec(x_189);
x_284 = lean_ctor_get(x_198, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_198, 1);
lean_inc(x_285);
lean_dec_ref(x_198);
x_286 = lean_ctor_get(x_192, 1);
x_287 = lean_ctor_get(x_192, 2);
x_301 = !lean_is_exclusive(x_192);
if (x_301 == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_192, 4);
lean_dec(x_302);
x_303 = lean_ctor_get(x_192, 3);
lean_dec(x_303);
x_304 = lean_ctor_get(x_192, 0);
lean_dec(x_304);
x_288 = x_192;
x_289 = x_301;
goto block_300;
}
else
{
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_192);
x_288 = lean_box(0);
x_289 = x_301;
goto block_300;
}
block_300:
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_unsigned_to_nat(3u);
if (x_289 == 0)
{
lean_ctor_set(x_288, 4, x_193);
lean_ctor_set(x_288, 3, x_193);
lean_ctor_set(x_288, 2, x_285);
lean_ctor_set(x_288, 1, x_284);
lean_ctor_set(x_288, 0, x_194);
x_291 = x_288;
goto block_298;
}
else
{
lean_object* x_299; 
x_299 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_299, 0, x_194);
lean_ctor_set(x_299, 1, x_284);
lean_ctor_set(x_299, 2, x_285);
lean_ctor_set(x_299, 3, x_193);
lean_ctor_set(x_299, 4, x_193);
x_291 = x_299;
goto block_298;
}
block_298:
{
lean_object* x_292; 
if (x_272 == 0)
{
lean_ctor_set(x_271, 3, x_193);
lean_ctor_set(x_271, 0, x_194);
x_292 = x_271;
goto block_296;
}
else
{
lean_object* x_297; 
x_297 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_297, 0, x_194);
lean_ctor_set(x_297, 1, x_190);
lean_ctor_set(x_297, 2, x_191);
lean_ctor_set(x_297, 3, x_193);
lean_ctor_set(x_297, 4, x_193);
x_292 = x_297;
goto block_296;
}
block_296:
{
lean_object* x_293; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_292);
lean_ctor_set(x_196, 3, x_291);
lean_ctor_set(x_196, 2, x_287);
lean_ctor_set(x_196, 1, x_286);
lean_ctor_set(x_196, 0, x_290);
x_293 = x_196;
goto block_294;
}
else
{
lean_object* x_295; 
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_290);
lean_ctor_set(x_295, 1, x_286);
lean_ctor_set(x_295, 2, x_287);
lean_ctor_set(x_295, 3, x_291);
lean_ctor_set(x_295, 4, x_292);
x_293 = x_295;
goto block_294;
}
block_294:
{
return x_293;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_189);
x_305 = lean_ctor_get(x_198, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_198, 1);
lean_inc(x_306);
lean_dec_ref(x_198);
x_307 = lean_unsigned_to_nat(3u);
if (x_272 == 0)
{
lean_ctor_set(x_271, 4, x_192);
lean_ctor_set(x_271, 2, x_306);
lean_ctor_set(x_271, 1, x_305);
lean_ctor_set(x_271, 0, x_194);
x_308 = x_271;
goto block_312;
}
else
{
lean_object* x_313; 
x_313 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_313, 0, x_194);
lean_ctor_set(x_313, 1, x_305);
lean_ctor_set(x_313, 2, x_306);
lean_ctor_set(x_313, 3, x_192);
lean_ctor_set(x_313, 4, x_192);
x_308 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_309; 
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_193);
lean_ctor_set(x_196, 3, x_308);
lean_ctor_set(x_196, 2, x_191);
lean_ctor_set(x_196, 1, x_190);
lean_ctor_set(x_196, 0, x_307);
x_309 = x_196;
goto block_310;
}
else
{
lean_object* x_311; 
x_311 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_311, 0, x_307);
lean_ctor_set(x_311, 1, x_190);
lean_ctor_set(x_311, 2, x_191);
lean_ctor_set(x_311, 3, x_308);
lean_ctor_set(x_311, 4, x_193);
x_309 = x_311;
goto block_310;
}
block_310:
{
return x_309;
}
}
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; 
x_314 = lean_ctor_get(x_198, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_198, 1);
lean_inc(x_315);
lean_dec_ref(x_198);
if (x_272 == 0)
{
lean_ctor_set(x_271, 3, x_193);
x_316 = x_271;
goto block_321;
}
else
{
lean_object* x_322; 
x_322 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_322, 0, x_189);
lean_ctor_set(x_322, 1, x_190);
lean_ctor_set(x_322, 2, x_191);
lean_ctor_set(x_322, 3, x_193);
lean_ctor_set(x_322, 4, x_193);
x_316 = x_322;
goto block_321;
}
block_321:
{
lean_object* x_317; lean_object* x_318; 
x_317 = lean_unsigned_to_nat(2u);
if (x_197 == 0)
{
lean_ctor_set(x_196, 4, x_316);
lean_ctor_set(x_196, 3, x_193);
lean_ctor_set(x_196, 2, x_315);
lean_ctor_set(x_196, 1, x_314);
lean_ctor_set(x_196, 0, x_317);
x_318 = x_196;
goto block_319;
}
else
{
lean_object* x_320; 
x_320 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_320, 0, x_317);
lean_ctor_set(x_320, 1, x_314);
lean_ctor_set(x_320, 2, x_315);
lean_ctor_set(x_320, 3, x_193);
lean_ctor_set(x_320, 4, x_316);
x_318 = x_320;
goto block_319;
}
block_319:
{
return x_318;
}
}
}
}
}
}
}
}
else
{
lean_object* x_337; uint8_t x_338; uint8_t x_489; 
lean_inc(x_193);
lean_inc(x_191);
lean_inc(x_190);
x_489 = !lean_is_exclusive(x_6);
if (x_489 == 0)
{
lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_490 = lean_ctor_get(x_6, 4);
lean_dec(x_490);
x_491 = lean_ctor_get(x_6, 3);
lean_dec(x_491);
x_492 = lean_ctor_get(x_6, 2);
lean_dec(x_492);
x_493 = lean_ctor_get(x_6, 1);
lean_dec(x_493);
x_494 = lean_ctor_get(x_6, 0);
lean_dec(x_494);
x_337 = x_6;
x_338 = x_489;
goto block_488;
}
else
{
lean_dec(x_6);
x_337 = lean_box(0);
x_338 = x_489;
goto block_488;
}
block_488:
{
lean_object* x_339; lean_object* x_340; 
x_339 = l_Std_DTreeMap_Internal_Impl_minView___redArg(x_190, x_191, x_192, x_193);
x_340 = lean_ctor_get(x_339, 2);
lean_inc(x_340);
if (lean_obj_tag(x_340) == 0)
{
lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; 
x_341 = lean_ctor_get(x_339, 0);
lean_inc(x_341);
x_342 = lean_ctor_get(x_339, 1);
lean_inc(x_342);
lean_dec_ref(x_339);
x_343 = lean_ctor_get(x_340, 0);
x_344 = lean_unsigned_to_nat(3u);
x_345 = lean_nat_mul(x_344, x_343);
x_346 = lean_nat_dec_lt(x_345, x_184);
lean_dec(x_345);
if (x_346 == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; 
lean_dec(x_188);
x_347 = lean_nat_add(x_194, x_184);
x_348 = lean_nat_add(x_347, x_343);
lean_dec(x_347);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_5);
lean_ctor_set(x_337, 2, x_342);
lean_ctor_set(x_337, 1, x_341);
lean_ctor_set(x_337, 0, x_348);
x_349 = x_337;
goto block_350;
}
else
{
lean_object* x_351; 
x_351 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_351, 0, x_348);
lean_ctor_set(x_351, 1, x_341);
lean_ctor_set(x_351, 2, x_342);
lean_ctor_set(x_351, 3, x_5);
lean_ctor_set(x_351, 4, x_340);
x_349 = x_351;
goto block_350;
}
block_350:
{
return x_349;
}
}
else
{
lean_object* x_352; uint8_t x_353; uint8_t x_417; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_417 = !lean_is_exclusive(x_5);
if (x_417 == 0)
{
lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
x_418 = lean_ctor_get(x_5, 4);
lean_dec(x_418);
x_419 = lean_ctor_get(x_5, 3);
lean_dec(x_419);
x_420 = lean_ctor_get(x_5, 2);
lean_dec(x_420);
x_421 = lean_ctor_get(x_5, 1);
lean_dec(x_421);
x_422 = lean_ctor_get(x_5, 0);
lean_dec(x_422);
x_352 = x_5;
x_353 = x_417;
goto block_416;
}
else
{
lean_dec(x_5);
x_352 = lean_box(0);
x_353 = x_417;
goto block_416;
}
block_416:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
x_354 = lean_ctor_get(x_187, 0);
x_355 = lean_ctor_get(x_188, 0);
x_356 = lean_ctor_get(x_188, 1);
x_357 = lean_ctor_get(x_188, 2);
x_358 = lean_ctor_get(x_188, 3);
x_359 = lean_ctor_get(x_188, 4);
x_360 = lean_unsigned_to_nat(2u);
x_361 = lean_nat_mul(x_360, x_354);
x_362 = lean_nat_dec_lt(x_355, x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; uint8_t x_364; uint8_t x_400; 
lean_inc(x_359);
lean_inc(x_358);
lean_inc(x_357);
lean_inc(x_356);
lean_del_object(x_352);
x_400 = !lean_is_exclusive(x_188);
if (x_400 == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
x_401 = lean_ctor_get(x_188, 4);
lean_dec(x_401);
x_402 = lean_ctor_get(x_188, 3);
lean_dec(x_402);
x_403 = lean_ctor_get(x_188, 2);
lean_dec(x_403);
x_404 = lean_ctor_get(x_188, 1);
lean_dec(x_404);
x_405 = lean_ctor_get(x_188, 0);
lean_dec(x_405);
x_363 = x_188;
x_364 = x_400;
goto block_399;
}
else
{
lean_dec(x_188);
x_363 = lean_box(0);
x_364 = x_400;
goto block_399;
}
block_399:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_387; lean_object* x_388; 
x_365 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_366 = lean_nat_add(x_365, x_343);
lean_dec(x_365);
x_387 = lean_nat_add(x_194, x_354);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_397; 
x_397 = lean_ctor_get(x_358, 0);
lean_inc(x_397);
x_388 = x_397;
goto block_396;
}
else
{
lean_object* x_398; 
x_398 = lean_unsigned_to_nat(0u);
x_388 = x_398;
goto block_396;
}
block_386:
{
lean_object* x_370; lean_object* x_371; 
x_370 = lean_nat_add(x_367, x_369);
lean_dec(x_369);
lean_dec(x_367);
lean_inc_ref(x_340);
if (x_364 == 0)
{
lean_ctor_set(x_363, 4, x_340);
lean_ctor_set(x_363, 3, x_359);
lean_ctor_set(x_363, 2, x_342);
lean_ctor_set(x_363, 1, x_341);
lean_ctor_set(x_363, 0, x_370);
x_371 = x_363;
goto block_384;
}
else
{
lean_object* x_385; 
x_385 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_385, 0, x_370);
lean_ctor_set(x_385, 1, x_341);
lean_ctor_set(x_385, 2, x_342);
lean_ctor_set(x_385, 3, x_359);
lean_ctor_set(x_385, 4, x_340);
x_371 = x_385;
goto block_384;
}
block_384:
{
lean_object* x_372; uint8_t x_373; uint8_t x_378; 
x_378 = !lean_is_exclusive(x_340);
if (x_378 == 0)
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_379 = lean_ctor_get(x_340, 4);
lean_dec(x_379);
x_380 = lean_ctor_get(x_340, 3);
lean_dec(x_380);
x_381 = lean_ctor_get(x_340, 2);
lean_dec(x_381);
x_382 = lean_ctor_get(x_340, 1);
lean_dec(x_382);
x_383 = lean_ctor_get(x_340, 0);
lean_dec(x_383);
x_372 = x_340;
x_373 = x_378;
goto block_377;
}
else
{
lean_dec(x_340);
x_372 = lean_box(0);
x_373 = x_378;
goto block_377;
}
block_377:
{
lean_object* x_374; 
if (x_373 == 0)
{
lean_ctor_set(x_372, 4, x_371);
lean_ctor_set(x_372, 3, x_368);
lean_ctor_set(x_372, 2, x_357);
lean_ctor_set(x_372, 1, x_356);
lean_ctor_set(x_372, 0, x_366);
x_374 = x_372;
goto block_375;
}
else
{
lean_object* x_376; 
x_376 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_376, 0, x_366);
lean_ctor_set(x_376, 1, x_356);
lean_ctor_set(x_376, 2, x_357);
lean_ctor_set(x_376, 3, x_368);
lean_ctor_set(x_376, 4, x_371);
x_374 = x_376;
goto block_375;
}
block_375:
{
return x_374;
}
}
}
}
block_396:
{
lean_object* x_389; lean_object* x_390; 
x_389 = lean_nat_add(x_387, x_388);
lean_dec(x_388);
lean_dec(x_387);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_358);
lean_ctor_set(x_337, 3, x_187);
lean_ctor_set(x_337, 2, x_186);
lean_ctor_set(x_337, 1, x_185);
lean_ctor_set(x_337, 0, x_389);
x_390 = x_337;
goto block_394;
}
else
{
lean_object* x_395; 
x_395 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_395, 0, x_389);
lean_ctor_set(x_395, 1, x_185);
lean_ctor_set(x_395, 2, x_186);
lean_ctor_set(x_395, 3, x_187);
lean_ctor_set(x_395, 4, x_358);
x_390 = x_395;
goto block_394;
}
block_394:
{
lean_object* x_391; 
x_391 = lean_nat_add(x_194, x_343);
if (lean_obj_tag(x_359) == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_359, 0);
lean_inc(x_392);
x_367 = x_391;
x_368 = x_390;
x_369 = x_392;
goto block_386;
}
else
{
lean_object* x_393; 
x_393 = lean_unsigned_to_nat(0u);
x_367 = x_391;
x_368 = x_390;
x_369 = x_393;
goto block_386;
}
}
}
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_406 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_407 = lean_nat_add(x_406, x_343);
lean_dec(x_406);
x_408 = lean_nat_add(x_194, x_343);
x_409 = lean_nat_add(x_408, x_355);
lean_dec(x_408);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_342);
lean_ctor_set(x_337, 1, x_341);
lean_ctor_set(x_337, 0, x_409);
x_410 = x_337;
goto block_414;
}
else
{
lean_object* x_415; 
x_415 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_415, 0, x_409);
lean_ctor_set(x_415, 1, x_341);
lean_ctor_set(x_415, 2, x_342);
lean_ctor_set(x_415, 3, x_188);
lean_ctor_set(x_415, 4, x_340);
x_410 = x_415;
goto block_414;
}
block_414:
{
lean_object* x_411; 
if (x_353 == 0)
{
lean_ctor_set(x_352, 4, x_410);
lean_ctor_set(x_352, 0, x_407);
x_411 = x_352;
goto block_412;
}
else
{
lean_object* x_413; 
x_413 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_413, 0, x_407);
lean_ctor_set(x_413, 1, x_185);
lean_ctor_set(x_413, 2, x_186);
lean_ctor_set(x_413, 3, x_187);
lean_ctor_set(x_413, 4, x_410);
x_411 = x_413;
goto block_412;
}
block_412:
{
return x_411;
}
}
}
}
}
}
else
{
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_423; uint8_t x_424; uint8_t x_446; 
lean_inc_ref(x_187);
lean_inc(x_186);
lean_inc(x_185);
lean_inc(x_184);
x_446 = !lean_is_exclusive(x_5);
if (x_446 == 0)
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_447 = lean_ctor_get(x_5, 4);
lean_dec(x_447);
x_448 = lean_ctor_get(x_5, 3);
lean_dec(x_448);
x_449 = lean_ctor_get(x_5, 2);
lean_dec(x_449);
x_450 = lean_ctor_get(x_5, 1);
lean_dec(x_450);
x_451 = lean_ctor_get(x_5, 0);
lean_dec(x_451);
x_423 = x_5;
x_424 = x_446;
goto block_445;
}
else
{
lean_dec(x_5);
x_423 = lean_box(0);
x_424 = x_446;
goto block_445;
}
block_445:
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; 
x_425 = lean_ctor_get(x_339, 0);
lean_inc(x_425);
x_426 = lean_ctor_get(x_339, 1);
lean_inc(x_426);
lean_dec_ref(x_339);
x_427 = lean_ctor_get(x_188, 0);
x_428 = lean_nat_add(x_194, x_184);
lean_dec(x_184);
x_429 = lean_nat_add(x_194, x_427);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_340);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_426);
lean_ctor_set(x_337, 1, x_425);
lean_ctor_set(x_337, 0, x_429);
x_430 = x_337;
goto block_434;
}
else
{
lean_object* x_435; 
x_435 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_435, 0, x_429);
lean_ctor_set(x_435, 1, x_425);
lean_ctor_set(x_435, 2, x_426);
lean_ctor_set(x_435, 3, x_188);
lean_ctor_set(x_435, 4, x_340);
x_430 = x_435;
goto block_434;
}
block_434:
{
lean_object* x_431; 
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_430);
lean_ctor_set(x_423, 0, x_428);
x_431 = x_423;
goto block_432;
}
else
{
lean_object* x_433; 
x_433 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_433, 0, x_428);
lean_ctor_set(x_433, 1, x_185);
lean_ctor_set(x_433, 2, x_186);
lean_ctor_set(x_433, 3, x_187);
lean_ctor_set(x_433, 4, x_430);
x_431 = x_433;
goto block_432;
}
block_432:
{
return x_431;
}
}
}
else
{
lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_184);
x_436 = lean_ctor_get(x_339, 0);
lean_inc(x_436);
x_437 = lean_ctor_get(x_339, 1);
lean_inc(x_437);
lean_dec_ref(x_339);
x_438 = lean_unsigned_to_nat(3u);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_188);
lean_ctor_set(x_337, 3, x_188);
lean_ctor_set(x_337, 2, x_437);
lean_ctor_set(x_337, 1, x_436);
lean_ctor_set(x_337, 0, x_194);
x_439 = x_337;
goto block_443;
}
else
{
lean_object* x_444; 
x_444 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_444, 0, x_194);
lean_ctor_set(x_444, 1, x_436);
lean_ctor_set(x_444, 2, x_437);
lean_ctor_set(x_444, 3, x_188);
lean_ctor_set(x_444, 4, x_188);
x_439 = x_444;
goto block_443;
}
block_443:
{
lean_object* x_440; 
if (x_424 == 0)
{
lean_ctor_set(x_423, 4, x_439);
lean_ctor_set(x_423, 0, x_438);
x_440 = x_423;
goto block_441;
}
else
{
lean_object* x_442; 
x_442 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_442, 0, x_438);
lean_ctor_set(x_442, 1, x_185);
lean_ctor_set(x_442, 2, x_186);
lean_ctor_set(x_442, 3, x_187);
lean_ctor_set(x_442, 4, x_439);
x_440 = x_442;
goto block_441;
}
block_441:
{
return x_440;
}
}
}
}
}
else
{
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_452; uint8_t x_453; uint8_t x_476; 
lean_inc(x_187);
lean_inc(x_186);
lean_inc(x_185);
x_476 = !lean_is_exclusive(x_5);
if (x_476 == 0)
{
lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
x_477 = lean_ctor_get(x_5, 4);
lean_dec(x_477);
x_478 = lean_ctor_get(x_5, 3);
lean_dec(x_478);
x_479 = lean_ctor_get(x_5, 2);
lean_dec(x_479);
x_480 = lean_ctor_get(x_5, 1);
lean_dec(x_480);
x_481 = lean_ctor_get(x_5, 0);
lean_dec(x_481);
x_452 = x_5;
x_453 = x_476;
goto block_475;
}
else
{
lean_dec(x_5);
x_452 = lean_box(0);
x_453 = x_476;
goto block_475;
}
block_475:
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; uint8_t x_459; uint8_t x_471; 
x_454 = lean_ctor_get(x_339, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_339, 1);
lean_inc(x_455);
lean_dec_ref(x_339);
x_456 = lean_ctor_get(x_188, 1);
x_457 = lean_ctor_get(x_188, 2);
x_471 = !lean_is_exclusive(x_188);
if (x_471 == 0)
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_188, 4);
lean_dec(x_472);
x_473 = lean_ctor_get(x_188, 3);
lean_dec(x_473);
x_474 = lean_ctor_get(x_188, 0);
lean_dec(x_474);
x_458 = x_188;
x_459 = x_471;
goto block_470;
}
else
{
lean_inc(x_457);
lean_inc(x_456);
lean_dec(x_188);
x_458 = lean_box(0);
x_459 = x_471;
goto block_470;
}
block_470:
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_unsigned_to_nat(3u);
if (x_459 == 0)
{
lean_ctor_set(x_458, 4, x_187);
lean_ctor_set(x_458, 3, x_187);
lean_ctor_set(x_458, 2, x_186);
lean_ctor_set(x_458, 1, x_185);
lean_ctor_set(x_458, 0, x_194);
x_461 = x_458;
goto block_468;
}
else
{
lean_object* x_469; 
x_469 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_469, 0, x_194);
lean_ctor_set(x_469, 1, x_185);
lean_ctor_set(x_469, 2, x_186);
lean_ctor_set(x_469, 3, x_187);
lean_ctor_set(x_469, 4, x_187);
x_461 = x_469;
goto block_468;
}
block_468:
{
lean_object* x_462; 
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_187);
lean_ctor_set(x_337, 3, x_187);
lean_ctor_set(x_337, 2, x_455);
lean_ctor_set(x_337, 1, x_454);
lean_ctor_set(x_337, 0, x_194);
x_462 = x_337;
goto block_466;
}
else
{
lean_object* x_467; 
x_467 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_467, 0, x_194);
lean_ctor_set(x_467, 1, x_454);
lean_ctor_set(x_467, 2, x_455);
lean_ctor_set(x_467, 3, x_187);
lean_ctor_set(x_467, 4, x_187);
x_462 = x_467;
goto block_466;
}
block_466:
{
lean_object* x_463; 
if (x_453 == 0)
{
lean_ctor_set(x_452, 4, x_462);
lean_ctor_set(x_452, 3, x_461);
lean_ctor_set(x_452, 2, x_457);
lean_ctor_set(x_452, 1, x_456);
lean_ctor_set(x_452, 0, x_460);
x_463 = x_452;
goto block_464;
}
else
{
lean_object* x_465; 
x_465 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_465, 0, x_460);
lean_ctor_set(x_465, 1, x_456);
lean_ctor_set(x_465, 2, x_457);
lean_ctor_set(x_465, 3, x_461);
lean_ctor_set(x_465, 4, x_462);
x_463 = x_465;
goto block_464;
}
block_464:
{
return x_463;
}
}
}
}
}
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
x_482 = lean_ctor_get(x_339, 0);
lean_inc(x_482);
x_483 = lean_ctor_get(x_339, 1);
lean_inc(x_483);
lean_dec_ref(x_339);
x_484 = lean_unsigned_to_nat(2u);
if (x_338 == 0)
{
lean_ctor_set(x_337, 4, x_188);
lean_ctor_set(x_337, 3, x_5);
lean_ctor_set(x_337, 2, x_483);
lean_ctor_set(x_337, 1, x_482);
lean_ctor_set(x_337, 0, x_484);
x_485 = x_337;
goto block_486;
}
else
{
lean_object* x_487; 
x_487 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_487, 0, x_484);
lean_ctor_set(x_487, 1, x_482);
lean_ctor_set(x_487, 2, x_483);
lean_ctor_set(x_487, 3, x_5);
lean_ctor_set(x_487, 4, x_188);
x_485 = x_487;
goto block_486;
}
block_486:
{
return x_485;
}
}
}
}
}
}
}
else
{
return x_5;
}
}
else
{
return x_6;
}
}
default: 
{
lean_object* x_495; lean_object* x_496; 
x_495 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_1, x_6);
x_496 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_495) == 0)
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; uint8_t x_505; 
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_5, 0);
x_499 = lean_ctor_get(x_5, 1);
x_500 = lean_ctor_get(x_5, 2);
x_501 = lean_ctor_get(x_5, 3);
x_502 = lean_ctor_get(x_5, 4);
lean_inc(x_502);
x_503 = lean_unsigned_to_nat(3u);
x_504 = lean_nat_mul(x_503, x_497);
x_505 = lean_nat_dec_lt(x_504, x_498);
lean_dec(x_504);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_502);
x_506 = lean_nat_add(x_496, x_498);
x_507 = lean_nat_add(x_506, x_497);
lean_dec(x_497);
lean_dec(x_506);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_495);
lean_ctor_set(x_7, 0, x_507);
x_508 = x_7;
goto block_509;
}
else
{
lean_object* x_510; 
x_510 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_510, 0, x_507);
lean_ctor_set(x_510, 1, x_3);
lean_ctor_set(x_510, 2, x_4);
lean_ctor_set(x_510, 3, x_5);
lean_ctor_set(x_510, 4, x_495);
x_508 = x_510;
goto block_509;
}
block_509:
{
return x_508;
}
}
else
{
lean_object* x_511; uint8_t x_512; uint8_t x_576; 
lean_inc(x_501);
lean_inc(x_500);
lean_inc(x_499);
lean_inc(x_498);
x_576 = !lean_is_exclusive(x_5);
if (x_576 == 0)
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
x_577 = lean_ctor_get(x_5, 4);
lean_dec(x_577);
x_578 = lean_ctor_get(x_5, 3);
lean_dec(x_578);
x_579 = lean_ctor_get(x_5, 2);
lean_dec(x_579);
x_580 = lean_ctor_get(x_5, 1);
lean_dec(x_580);
x_581 = lean_ctor_get(x_5, 0);
lean_dec(x_581);
x_511 = x_5;
x_512 = x_576;
goto block_575;
}
else
{
lean_dec(x_5);
x_511 = lean_box(0);
x_512 = x_576;
goto block_575;
}
block_575:
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; uint8_t x_521; 
x_513 = lean_ctor_get(x_501, 0);
x_514 = lean_ctor_get(x_502, 0);
x_515 = lean_ctor_get(x_502, 1);
x_516 = lean_ctor_get(x_502, 2);
x_517 = lean_ctor_get(x_502, 3);
x_518 = lean_ctor_get(x_502, 4);
x_519 = lean_unsigned_to_nat(2u);
x_520 = lean_nat_mul(x_519, x_513);
x_521 = lean_nat_dec_lt(x_514, x_520);
lean_dec(x_520);
if (x_521 == 0)
{
lean_object* x_522; uint8_t x_523; uint8_t x_550; 
lean_inc(x_518);
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
x_550 = !lean_is_exclusive(x_502);
if (x_550 == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; 
x_551 = lean_ctor_get(x_502, 4);
lean_dec(x_551);
x_552 = lean_ctor_get(x_502, 3);
lean_dec(x_552);
x_553 = lean_ctor_get(x_502, 2);
lean_dec(x_553);
x_554 = lean_ctor_get(x_502, 1);
lean_dec(x_554);
x_555 = lean_ctor_get(x_502, 0);
lean_dec(x_555);
x_522 = x_502;
x_523 = x_550;
goto block_549;
}
else
{
lean_dec(x_502);
x_522 = lean_box(0);
x_523 = x_550;
goto block_549;
}
block_549:
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_537; lean_object* x_538; 
x_524 = lean_nat_add(x_496, x_498);
lean_dec(x_498);
x_525 = lean_nat_add(x_524, x_497);
lean_dec(x_524);
x_537 = lean_nat_add(x_496, x_513);
if (lean_obj_tag(x_517) == 0)
{
lean_object* x_547; 
x_547 = lean_ctor_get(x_517, 0);
lean_inc(x_547);
x_538 = x_547;
goto block_546;
}
else
{
lean_object* x_548; 
x_548 = lean_unsigned_to_nat(0u);
x_538 = x_548;
goto block_546;
}
block_536:
{
lean_object* x_529; lean_object* x_530; 
x_529 = lean_nat_add(x_526, x_528);
lean_dec(x_528);
lean_dec(x_526);
if (x_523 == 0)
{
lean_ctor_set(x_522, 4, x_495);
lean_ctor_set(x_522, 3, x_518);
lean_ctor_set(x_522, 2, x_4);
lean_ctor_set(x_522, 1, x_3);
lean_ctor_set(x_522, 0, x_529);
x_530 = x_522;
goto block_534;
}
else
{
lean_object* x_535; 
x_535 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_535, 0, x_529);
lean_ctor_set(x_535, 1, x_3);
lean_ctor_set(x_535, 2, x_4);
lean_ctor_set(x_535, 3, x_518);
lean_ctor_set(x_535, 4, x_495);
x_530 = x_535;
goto block_534;
}
block_534:
{
lean_object* x_531; 
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_530);
lean_ctor_set(x_511, 3, x_527);
lean_ctor_set(x_511, 2, x_516);
lean_ctor_set(x_511, 1, x_515);
lean_ctor_set(x_511, 0, x_525);
x_531 = x_511;
goto block_532;
}
else
{
lean_object* x_533; 
x_533 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_533, 0, x_525);
lean_ctor_set(x_533, 1, x_515);
lean_ctor_set(x_533, 2, x_516);
lean_ctor_set(x_533, 3, x_527);
lean_ctor_set(x_533, 4, x_530);
x_531 = x_533;
goto block_532;
}
block_532:
{
return x_531;
}
}
}
block_546:
{
lean_object* x_539; lean_object* x_540; 
x_539 = lean_nat_add(x_537, x_538);
lean_dec(x_538);
lean_dec(x_537);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_517);
lean_ctor_set(x_7, 3, x_501);
lean_ctor_set(x_7, 2, x_500);
lean_ctor_set(x_7, 1, x_499);
lean_ctor_set(x_7, 0, x_539);
x_540 = x_7;
goto block_544;
}
else
{
lean_object* x_545; 
x_545 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_545, 0, x_539);
lean_ctor_set(x_545, 1, x_499);
lean_ctor_set(x_545, 2, x_500);
lean_ctor_set(x_545, 3, x_501);
lean_ctor_set(x_545, 4, x_517);
x_540 = x_545;
goto block_544;
}
block_544:
{
lean_object* x_541; 
x_541 = lean_nat_add(x_496, x_497);
lean_dec(x_497);
if (lean_obj_tag(x_518) == 0)
{
lean_object* x_542; 
x_542 = lean_ctor_get(x_518, 0);
lean_inc(x_542);
x_526 = x_541;
x_527 = x_540;
x_528 = x_542;
goto block_536;
}
else
{
lean_object* x_543; 
x_543 = lean_unsigned_to_nat(0u);
x_526 = x_541;
x_527 = x_540;
x_528 = x_543;
goto block_536;
}
}
}
}
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; 
lean_del_object(x_7);
x_556 = lean_nat_add(x_496, x_498);
lean_dec(x_498);
x_557 = lean_nat_add(x_556, x_497);
lean_dec(x_556);
x_558 = lean_nat_add(x_496, x_497);
lean_dec(x_497);
x_559 = lean_nat_add(x_558, x_514);
lean_dec(x_558);
lean_inc_ref(x_495);
if (x_512 == 0)
{
lean_ctor_set(x_511, 4, x_495);
lean_ctor_set(x_511, 3, x_502);
lean_ctor_set(x_511, 2, x_4);
lean_ctor_set(x_511, 1, x_3);
lean_ctor_set(x_511, 0, x_559);
x_560 = x_511;
goto block_573;
}
else
{
lean_object* x_574; 
x_574 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_574, 0, x_559);
lean_ctor_set(x_574, 1, x_3);
lean_ctor_set(x_574, 2, x_4);
lean_ctor_set(x_574, 3, x_502);
lean_ctor_set(x_574, 4, x_495);
x_560 = x_574;
goto block_573;
}
block_573:
{
lean_object* x_561; uint8_t x_562; uint8_t x_567; 
x_567 = !lean_is_exclusive(x_495);
if (x_567 == 0)
{
lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; 
x_568 = lean_ctor_get(x_495, 4);
lean_dec(x_568);
x_569 = lean_ctor_get(x_495, 3);
lean_dec(x_569);
x_570 = lean_ctor_get(x_495, 2);
lean_dec(x_570);
x_571 = lean_ctor_get(x_495, 1);
lean_dec(x_571);
x_572 = lean_ctor_get(x_495, 0);
lean_dec(x_572);
x_561 = x_495;
x_562 = x_567;
goto block_566;
}
else
{
lean_dec(x_495);
x_561 = lean_box(0);
x_562 = x_567;
goto block_566;
}
block_566:
{
lean_object* x_563; 
if (x_562 == 0)
{
lean_ctor_set(x_561, 4, x_560);
lean_ctor_set(x_561, 3, x_501);
lean_ctor_set(x_561, 2, x_500);
lean_ctor_set(x_561, 1, x_499);
lean_ctor_set(x_561, 0, x_557);
x_563 = x_561;
goto block_564;
}
else
{
lean_object* x_565; 
x_565 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_565, 0, x_557);
lean_ctor_set(x_565, 1, x_499);
lean_ctor_set(x_565, 2, x_500);
lean_ctor_set(x_565, 3, x_501);
lean_ctor_set(x_565, 4, x_560);
x_563 = x_565;
goto block_564;
}
block_564:
{
return x_563;
}
}
}
}
}
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; 
x_582 = lean_ctor_get(x_495, 0);
lean_inc(x_582);
x_583 = lean_nat_add(x_496, x_582);
lean_dec(x_582);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_495);
lean_ctor_set(x_7, 0, x_583);
x_584 = x_7;
goto block_585;
}
else
{
lean_object* x_586; 
x_586 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_3);
lean_ctor_set(x_586, 2, x_4);
lean_ctor_set(x_586, 3, x_5);
lean_ctor_set(x_586, 4, x_495);
x_584 = x_586;
goto block_585;
}
block_585:
{
return x_584;
}
}
}
else
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_587; 
x_587 = lean_ctor_get(x_5, 3);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; 
lean_inc_ref(x_587);
x_588 = lean_ctor_get(x_5, 4);
lean_inc(x_588);
if (lean_obj_tag(x_588) == 0)
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; uint8_t x_604; 
x_589 = lean_ctor_get(x_5, 0);
x_590 = lean_ctor_get(x_5, 1);
x_591 = lean_ctor_get(x_5, 2);
x_604 = !lean_is_exclusive(x_5);
if (x_604 == 0)
{
lean_object* x_605; lean_object* x_606; 
x_605 = lean_ctor_get(x_5, 4);
lean_dec(x_605);
x_606 = lean_ctor_get(x_5, 3);
lean_dec(x_606);
x_592 = x_5;
x_593 = x_604;
goto block_603;
}
else
{
lean_inc(x_591);
lean_inc(x_590);
lean_inc(x_589);
lean_dec(x_5);
x_592 = lean_box(0);
x_593 = x_604;
goto block_603;
}
block_603:
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; 
x_594 = lean_ctor_get(x_588, 0);
x_595 = lean_nat_add(x_496, x_589);
lean_dec(x_589);
x_596 = lean_nat_add(x_496, x_594);
if (x_593 == 0)
{
lean_ctor_set(x_592, 4, x_495);
lean_ctor_set(x_592, 3, x_588);
lean_ctor_set(x_592, 2, x_4);
lean_ctor_set(x_592, 1, x_3);
lean_ctor_set(x_592, 0, x_596);
x_597 = x_592;
goto block_601;
}
else
{
lean_object* x_602; 
x_602 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_602, 0, x_596);
lean_ctor_set(x_602, 1, x_3);
lean_ctor_set(x_602, 2, x_4);
lean_ctor_set(x_602, 3, x_588);
lean_ctor_set(x_602, 4, x_495);
x_597 = x_602;
goto block_601;
}
block_601:
{
lean_object* x_598; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_597);
lean_ctor_set(x_7, 3, x_587);
lean_ctor_set(x_7, 2, x_591);
lean_ctor_set(x_7, 1, x_590);
lean_ctor_set(x_7, 0, x_595);
x_598 = x_7;
goto block_599;
}
else
{
lean_object* x_600; 
x_600 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_600, 0, x_595);
lean_ctor_set(x_600, 1, x_590);
lean_ctor_set(x_600, 2, x_591);
lean_ctor_set(x_600, 3, x_587);
lean_ctor_set(x_600, 4, x_597);
x_598 = x_600;
goto block_599;
}
block_599:
{
return x_598;
}
}
}
}
else
{
lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; uint8_t x_619; 
x_607 = lean_ctor_get(x_5, 1);
x_608 = lean_ctor_get(x_5, 2);
x_619 = !lean_is_exclusive(x_5);
if (x_619 == 0)
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; 
x_620 = lean_ctor_get(x_5, 4);
lean_dec(x_620);
x_621 = lean_ctor_get(x_5, 3);
lean_dec(x_621);
x_622 = lean_ctor_get(x_5, 0);
lean_dec(x_622);
x_609 = x_5;
x_610 = x_619;
goto block_618;
}
else
{
lean_inc(x_608);
lean_inc(x_607);
lean_dec(x_5);
x_609 = lean_box(0);
x_610 = x_619;
goto block_618;
}
block_618:
{
lean_object* x_611; lean_object* x_612; 
x_611 = lean_unsigned_to_nat(3u);
if (x_610 == 0)
{
lean_ctor_set(x_609, 3, x_588);
lean_ctor_set(x_609, 2, x_4);
lean_ctor_set(x_609, 1, x_3);
lean_ctor_set(x_609, 0, x_496);
x_612 = x_609;
goto block_616;
}
else
{
lean_object* x_617; 
x_617 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_617, 0, x_496);
lean_ctor_set(x_617, 1, x_3);
lean_ctor_set(x_617, 2, x_4);
lean_ctor_set(x_617, 3, x_588);
lean_ctor_set(x_617, 4, x_588);
x_612 = x_617;
goto block_616;
}
block_616:
{
lean_object* x_613; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_612);
lean_ctor_set(x_7, 3, x_587);
lean_ctor_set(x_7, 2, x_608);
lean_ctor_set(x_7, 1, x_607);
lean_ctor_set(x_7, 0, x_611);
x_613 = x_7;
goto block_614;
}
else
{
lean_object* x_615; 
x_615 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_615, 0, x_611);
lean_ctor_set(x_615, 1, x_607);
lean_ctor_set(x_615, 2, x_608);
lean_ctor_set(x_615, 3, x_587);
lean_ctor_set(x_615, 4, x_612);
x_613 = x_615;
goto block_614;
}
block_614:
{
return x_613;
}
}
}
}
}
else
{
lean_object* x_623; 
x_623 = lean_ctor_get(x_5, 4);
lean_inc(x_623);
if (lean_obj_tag(x_623) == 0)
{
lean_object* x_624; lean_object* x_625; lean_object* x_626; uint8_t x_627; uint8_t x_648; 
lean_inc(x_587);
x_624 = lean_ctor_get(x_5, 1);
x_625 = lean_ctor_get(x_5, 2);
x_648 = !lean_is_exclusive(x_5);
if (x_648 == 0)
{
lean_object* x_649; lean_object* x_650; lean_object* x_651; 
x_649 = lean_ctor_get(x_5, 4);
lean_dec(x_649);
x_650 = lean_ctor_get(x_5, 3);
lean_dec(x_650);
x_651 = lean_ctor_get(x_5, 0);
lean_dec(x_651);
x_626 = x_5;
x_627 = x_648;
goto block_647;
}
else
{
lean_inc(x_625);
lean_inc(x_624);
lean_dec(x_5);
x_626 = lean_box(0);
x_627 = x_648;
goto block_647;
}
block_647:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; uint8_t x_643; 
x_628 = lean_ctor_get(x_623, 1);
x_629 = lean_ctor_get(x_623, 2);
x_643 = !lean_is_exclusive(x_623);
if (x_643 == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; 
x_644 = lean_ctor_get(x_623, 4);
lean_dec(x_644);
x_645 = lean_ctor_get(x_623, 3);
lean_dec(x_645);
x_646 = lean_ctor_get(x_623, 0);
lean_dec(x_646);
x_630 = x_623;
x_631 = x_643;
goto block_642;
}
else
{
lean_inc(x_629);
lean_inc(x_628);
lean_dec(x_623);
x_630 = lean_box(0);
x_631 = x_643;
goto block_642;
}
block_642:
{
lean_object* x_632; lean_object* x_633; 
x_632 = lean_unsigned_to_nat(3u);
if (x_631 == 0)
{
lean_ctor_set(x_630, 4, x_587);
lean_ctor_set(x_630, 3, x_587);
lean_ctor_set(x_630, 2, x_625);
lean_ctor_set(x_630, 1, x_624);
lean_ctor_set(x_630, 0, x_496);
x_633 = x_630;
goto block_640;
}
else
{
lean_object* x_641; 
x_641 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_641, 0, x_496);
lean_ctor_set(x_641, 1, x_624);
lean_ctor_set(x_641, 2, x_625);
lean_ctor_set(x_641, 3, x_587);
lean_ctor_set(x_641, 4, x_587);
x_633 = x_641;
goto block_640;
}
block_640:
{
lean_object* x_634; 
if (x_627 == 0)
{
lean_ctor_set(x_626, 4, x_587);
lean_ctor_set(x_626, 2, x_4);
lean_ctor_set(x_626, 1, x_3);
lean_ctor_set(x_626, 0, x_496);
x_634 = x_626;
goto block_638;
}
else
{
lean_object* x_639; 
x_639 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_639, 0, x_496);
lean_ctor_set(x_639, 1, x_3);
lean_ctor_set(x_639, 2, x_4);
lean_ctor_set(x_639, 3, x_587);
lean_ctor_set(x_639, 4, x_587);
x_634 = x_639;
goto block_638;
}
block_638:
{
lean_object* x_635; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_634);
lean_ctor_set(x_7, 3, x_633);
lean_ctor_set(x_7, 2, x_629);
lean_ctor_set(x_7, 1, x_628);
lean_ctor_set(x_7, 0, x_632);
x_635 = x_7;
goto block_636;
}
else
{
lean_object* x_637; 
x_637 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_637, 0, x_632);
lean_ctor_set(x_637, 1, x_628);
lean_ctor_set(x_637, 2, x_629);
lean_ctor_set(x_637, 3, x_633);
lean_ctor_set(x_637, 4, x_634);
x_635 = x_637;
goto block_636;
}
block_636:
{
return x_635;
}
}
}
}
}
}
else
{
lean_object* x_652; lean_object* x_653; 
x_652 = lean_unsigned_to_nat(2u);
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_623);
lean_ctor_set(x_7, 0, x_652);
x_653 = x_7;
goto block_654;
}
else
{
lean_object* x_655; 
x_655 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_655, 0, x_652);
lean_ctor_set(x_655, 1, x_3);
lean_ctor_set(x_655, 2, x_4);
lean_ctor_set(x_655, 3, x_5);
lean_ctor_set(x_655, 4, x_623);
x_653 = x_655;
goto block_654;
}
block_654:
{
return x_653;
}
}
}
}
else
{
lean_object* x_656; 
if (x_8 == 0)
{
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 0, x_496);
x_656 = x_7;
goto block_657;
}
else
{
lean_object* x_658; 
x_658 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_658, 0, x_496);
lean_ctor_set(x_658, 1, x_3);
lean_ctor_set(x_658, 2, x_4);
lean_ctor_set(x_658, 3, x_5);
lean_ctor_set(x_658, 4, x_5);
x_656 = x_658;
goto block_657;
}
block_657:
{
return x_656;
}
}
}
}
}
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5_spec__8___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_instHashableFVarId_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5_spec__8___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__4___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_instBEqFVarId_beq(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_instHashableFVarId_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__4___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_71; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_71 = !lean_is_exclusive(x_2);
if (x_71 == 0)
{
x_12 = x_2;
x_13 = x_71;
goto block_70;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_71;
goto block_70;
}
block_70:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_10, x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_69; 
x_16 = lean_ctor_get(x_3, 1);
x_17 = lean_ctor_get(x_3, 0);
x_69 = !lean_is_exclusive(x_3);
if (x_69 == 0)
{
x_18 = x_3;
x_19 = x_69;
goto block_68;
}
else
{
lean_inc(x_16);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_box(0);
x_19 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_67; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
x_67 = !lean_is_exclusive(x_16);
if (x_67 == 0)
{
x_22 = x_16;
x_23 = x_67;
goto block_66;
}
else
{
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_box(0);
x_23 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_array_fget_borrowed(x_9, x_10);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 2);
x_27 = 0;
lean_inc_ref(x_26);
x_28 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_27, x_26, x_20, x_1);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = 0;
x_31 = l_Lean_Compiler_LCNF_mkAuxParam(x_27, x_29, x_30, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_add(x_10, x_34);
lean_dec(x_10);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_35);
x_36 = x_12;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_9);
lean_ctor_set(x_49, 1, x_35);
lean_ctor_set(x_49, 2, x_11);
x_36 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_array_push(x_17, x_32);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_33);
lean_inc_ref(x_38);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(x_20, x_25, x_38);
x_40 = lean_array_push(x_21, x_38);
if (x_23 == 0)
{
lean_ctor_set(x_22, 1, x_40);
lean_ctor_set(x_22, 0, x_39);
x_41 = x_22;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_39);
lean_ctor_set(x_47, 1, x_40);
x_41 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_42; 
if (x_19 == 0)
{
lean_ctor_set(x_18, 1, x_41);
lean_ctor_set(x_18, 0, x_37);
x_42 = x_18;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_41);
x_42 = x_45;
goto block_44;
}
block_44:
{
x_2 = x_36;
x_3 = x_42;
goto _start;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_dec(x_25);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_del_object(x_18);
lean_dec(x_17);
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_50 = lean_ctor_get(x_31, 0);
x_57 = !lean_is_exclusive(x_31);
if (x_57 == 0)
{
x_51 = x_31;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_31);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_65; 
lean_dec(x_25);
lean_del_object(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_del_object(x_18);
lean_dec(x_17);
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
x_58 = lean_ctor_get(x_28, 0);
x_65 = !lean_is_exclusive(x_28);
if (x_65 == 0)
{
x_59 = x_28;
x_60 = x_65;
goto block_64;
}
else
{
lean_inc(x_58);
lean_dec(x_28);
x_59 = lean_box(0);
x_60 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_61; 
if (x_60 == 0)
{
x_61 = x_59;
goto block_62;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_58);
x_61 = x_63;
goto block_62;
}
block_62:
{
return x_61;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_1, 3);
x_6 = lean_ctor_get(x_1, 4);
x_7 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_2, x_3);
switch (x_7) {
case 0:
{
x_1 = x_5;
goto _start;
}
case 1:
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
default: 
{
x_1 = x_6;
goto _start;
}
}
}
else
{
lean_object* x_11; 
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__2);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4));
x_2 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__3);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__5);
x_2 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_185; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_185 = !lean_is_exclusive(x_2);
if (x_185 == 0)
{
x_11 = x_2;
x_12 = x_185;
goto block_184;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_185;
goto block_184;
}
block_184:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
if (lean_obj_tag(x_10) == 5)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_10, 0);
x_46 = lean_ctor_get(x_9, 0);
x_47 = lean_ctor_get(x_9, 3);
lean_inc(x_47);
x_48 = l_Lean_instBEqFVarId_beq(x_46, x_45);
if (x_48 == 0)
{
lean_dec(x_47);
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_44;
}
else
{
if (lean_obj_tag(x_47) == 4)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_183; 
x_49 = lean_ctor_get(x_47, 0);
x_50 = lean_ctor_get(x_47, 1);
x_183 = !lean_is_exclusive(x_47);
if (x_183 == 0)
{
x_51 = x_47;
x_52 = x_183;
goto block_182;
}
else
{
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_47);
x_51 = lean_box(0);
x_52 = x_183;
goto block_182;
}
block_182:
{
lean_object* x_53; 
lean_inc(x_49);
x_53 = l_Lean_Compiler_LCNF_getBinderName(x_49, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec_ref(x_53);
x_55 = l_Lean_Name_getPrefix(x_54);
lean_dec(x_54);
x_56 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__1));
x_57 = lean_name_eq(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_del_object(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_44;
}
else
{
lean_object* x_58; 
lean_inc(x_49);
x_58 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_findFun_x3f___redArg(x_49, x_5);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
if (lean_obj_tag(x_59) == 1)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_165; 
lean_dec_ref(x_10);
lean_del_object(x_11);
x_60 = lean_ctor_get(x_59, 0);
x_165 = !lean_is_exclusive(x_59);
if (x_165 == 0)
{
x_61 = x_59;
x_62 = x_165;
goto block_164;
}
else
{
lean_inc(x_60);
lean_dec(x_59);
x_61 = lean_box(0);
x_62 = x_165;
goto block_164;
}
block_164:
{
uint8_t x_63; lean_object* x_64; 
x_63 = 0;
x_64 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_63, x_9, x_5);
lean_dec_ref(x_9);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; uint8_t x_66; uint8_t x_154; 
x_154 = !lean_is_exclusive(x_64);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_64, 0);
lean_dec(x_155);
x_65 = x_64;
x_66 = x_154;
goto block_153;
}
else
{
lean_dec(x_64);
x_65 = lean_box(0);
x_66 = x_154;
goto block_153;
}
block_153:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_st_ref_get(x_3);
x_68 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_67, x_49);
lean_dec(x_67);
if (lean_obj_tag(x_68) == 1)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_del_object(x_61);
lean_dec(x_60);
lean_del_object(x_51);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_50);
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_71);
x_72 = x_65;
goto block_73;
}
else
{
lean_object* x_74; 
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_71);
x_72 = x_74;
goto block_73;
}
block_73:
{
return x_72;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_68);
lean_del_object(x_65);
x_75 = lean_ctor_get(x_60, 2);
lean_inc_ref(x_75);
lean_dec(x_60);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_array_get_size(x_50);
x_78 = l_Array_toSubarray___redArg(x_75, x_76, x_77);
x_79 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__6);
x_80 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_57, x_78, x_79, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; uint8_t x_144; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_82 = lean_ctor_get(x_81, 1);
x_83 = lean_ctor_get(x_81, 0);
x_144 = !lean_is_exclusive(x_81);
if (x_144 == 0)
{
x_84 = x_81;
x_85 = x_144;
goto block_143;
}
else
{
lean_inc(x_82);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_box(0);
x_85 = x_144;
goto block_143;
}
block_143:
{
lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_141; 
x_86 = lean_ctor_get(x_82, 1);
x_141 = !lean_is_exclusive(x_82);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_82, 0);
lean_dec(x_142);
x_87 = x_82;
x_88 = x_141;
goto block_140;
}
else
{
lean_inc(x_86);
lean_dec(x_82);
x_87 = lean_box(0);
x_88 = x_141;
goto block_140;
}
block_140:
{
lean_object* x_89; 
lean_inc(x_49);
if (x_52 == 0)
{
lean_ctor_set(x_51, 1, x_86);
x_89 = x_51;
goto block_138;
}
else
{
lean_object* x_139; 
x_139 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_139, 0, x_49);
lean_ctor_set(x_139, 1, x_86);
x_89 = x_139;
goto block_138;
}
block_138:
{
lean_object* x_90; lean_object* x_91; 
x_90 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_91 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_63, x_89, x_90, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_93 = lean_ctor_get(x_1, 0);
x_94 = lean_ctor_get(x_92, 0);
lean_inc(x_94);
if (x_62 == 0)
{
lean_ctor_set(x_61, 0, x_94);
x_95 = x_61;
goto block_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_94);
x_95 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_mk_empty_array_with_capacity(x_96);
x_98 = lean_array_push(x_97, x_95);
lean_inc(x_93);
if (x_88 == 0)
{
lean_ctor_set_tag(x_87, 3);
lean_ctor_set(x_87, 1, x_98);
lean_ctor_set(x_87, 0, x_93);
x_99 = x_87;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_127, 0, x_93);
lean_ctor_set(x_127, 1, x_98);
x_99 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_100; 
if (x_85 == 0)
{
lean_ctor_set(x_84, 1, x_99);
lean_ctor_set(x_84, 0, x_92);
x_100 = x_84;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_92);
lean_ctor_set(x_125, 1, x_99);
x_100 = x_125;
goto block_124;
}
block_124:
{
lean_object* x_101; lean_object* x_102; 
x_101 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10));
x_102 = l_Lean_Compiler_LCNF_mkAuxJpDecl(x_63, x_83, x_100, x_101, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_115; 
x_103 = lean_ctor_get(x_102, 0);
x_115 = !lean_is_exclusive(x_102);
if (x_115 == 0)
{
x_104 = x_102;
x_105 = x_115;
goto block_114;
}
else
{
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_box(0);
x_105 = x_115;
goto block_114;
}
block_114:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_st_ref_take(x_3);
lean_inc(x_103);
x_107 = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_FVarIdSet_insert_spec__1___redArg(x_49, x_103, x_106);
x_108 = lean_st_ref_set(x_3, x_107);
x_109 = lean_ctor_get(x_103, 0);
lean_inc(x_109);
lean_dec(x_103);
x_110 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_50);
if (x_105 == 0)
{
lean_ctor_set(x_104, 0, x_110);
x_111 = x_104;
goto block_112;
}
else
{
lean_object* x_113; 
x_113 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_113, 0, x_110);
x_111 = x_113;
goto block_112;
}
block_112:
{
return x_111;
}
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_123; 
lean_dec_ref(x_50);
lean_dec(x_49);
x_116 = lean_ctor_get(x_102, 0);
x_123 = !lean_is_exclusive(x_102);
if (x_123 == 0)
{
x_117 = x_102;
x_118 = x_123;
goto block_122;
}
else
{
lean_inc(x_116);
lean_dec(x_102);
x_117 = lean_box(0);
x_118 = x_123;
goto block_122;
}
block_122:
{
lean_object* x_119; 
if (x_118 == 0)
{
x_119 = x_117;
goto block_120;
}
else
{
lean_object* x_121; 
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_116);
x_119 = x_121;
goto block_120;
}
block_120:
{
return x_119;
}
}
}
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_137; 
lean_del_object(x_87);
lean_del_object(x_84);
lean_dec(x_83);
lean_del_object(x_61);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_130 = lean_ctor_get(x_91, 0);
x_137 = !lean_is_exclusive(x_91);
if (x_137 == 0)
{
x_131 = x_91;
x_132 = x_137;
goto block_136;
}
else
{
lean_inc(x_130);
lean_dec(x_91);
x_131 = lean_box(0);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_132 == 0)
{
x_133 = x_131;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_130);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; uint8_t x_152; 
lean_del_object(x_61);
lean_del_object(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_145 = lean_ctor_get(x_80, 0);
x_152 = !lean_is_exclusive(x_80);
if (x_152 == 0)
{
x_146 = x_80;
x_147 = x_152;
goto block_151;
}
else
{
lean_inc(x_145);
lean_dec(x_80);
x_146 = lean_box(0);
x_147 = x_152;
goto block_151;
}
block_151:
{
lean_object* x_148; 
if (x_147 == 0)
{
x_148 = x_146;
goto block_149;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_150, 0, x_145);
x_148 = x_150;
goto block_149;
}
block_149:
{
return x_148;
}
}
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; uint8_t x_158; uint8_t x_163; 
lean_del_object(x_61);
lean_dec(x_60);
lean_del_object(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_156 = lean_ctor_get(x_64, 0);
x_163 = !lean_is_exclusive(x_64);
if (x_163 == 0)
{
x_157 = x_64;
x_158 = x_163;
goto block_162;
}
else
{
lean_inc(x_156);
lean_dec(x_64);
x_157 = lean_box(0);
x_158 = x_163;
goto block_162;
}
block_162:
{
lean_object* x_159; 
if (x_158 == 0)
{
x_159 = x_157;
goto block_160;
}
else
{
lean_object* x_161; 
x_161 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_161, 0, x_156);
x_159 = x_161;
goto block_160;
}
block_160:
{
return x_159;
}
}
}
}
}
else
{
lean_dec(x_59);
lean_del_object(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_44;
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; uint8_t x_173; 
lean_del_object(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_10);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_166 = lean_ctor_get(x_58, 0);
x_173 = !lean_is_exclusive(x_58);
if (x_173 == 0)
{
x_167 = x_58;
x_168 = x_173;
goto block_172;
}
else
{
lean_inc(x_166);
lean_dec(x_58);
x_167 = lean_box(0);
x_168 = x_173;
goto block_172;
}
block_172:
{
lean_object* x_169; 
if (x_168 == 0)
{
x_169 = x_167;
goto block_170;
}
else
{
lean_object* x_171; 
x_171 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_171, 0, x_166);
x_169 = x_171;
goto block_170;
}
block_170:
{
return x_169;
}
}
}
}
}
else
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; uint8_t x_181; 
lean_del_object(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_10);
lean_del_object(x_11);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_174 = lean_ctor_get(x_53, 0);
x_181 = !lean_is_exclusive(x_53);
if (x_181 == 0)
{
x_175 = x_53;
x_176 = x_181;
goto block_180;
}
else
{
lean_inc(x_174);
lean_dec(x_53);
x_175 = lean_box(0);
x_176 = x_181;
goto block_180;
}
block_180:
{
lean_object* x_177; 
if (x_176 == 0)
{
x_177 = x_175;
goto block_178;
}
else
{
lean_object* x_179; 
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_174);
x_177 = x_179;
goto block_178;
}
block_178:
{
return x_177;
}
}
}
}
}
else
{
lean_dec(x_47);
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_44;
}
}
}
else
{
x_13 = x_3;
x_14 = x_4;
x_15 = x_5;
x_16 = x_6;
x_17 = x_7;
goto block_44;
}
block_44:
{
lean_object* x_18; 
x_18 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_10, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_43; 
x_19 = lean_ctor_get(x_18, 0);
x_43 = !lean_is_exclusive(x_18);
if (x_43 == 0)
{
x_20 = x_18;
x_21 = x_43;
goto block_42;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_st_ref_get(x_13);
x_23 = lean_ctor_get(x_9, 0);
x_24 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_22, x_23);
lean_dec(x_22);
if (lean_obj_tag(x_24) == 1)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_st_ref_take(x_13);
x_27 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_23, x_26);
x_28 = lean_st_ref_set(x_13, x_27);
if (x_12 == 0)
{
lean_ctor_set_tag(x_11, 2);
lean_ctor_set(x_11, 1, x_19);
lean_ctor_set(x_11, 0, x_25);
x_29 = x_11;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_25);
lean_ctor_set(x_35, 1, x_19);
x_29 = x_35;
goto block_34;
}
block_34:
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_29);
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_30);
x_31 = x_20;
goto block_32;
}
else
{
lean_object* x_33; 
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_30);
x_31 = x_33;
goto block_32;
}
block_32:
{
return x_31;
}
}
}
else
{
lean_object* x_36; 
lean_dec(x_24);
if (x_12 == 0)
{
lean_ctor_set(x_11, 1, x_19);
x_36 = x_11;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_9);
lean_ctor_set(x_41, 1, x_19);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 0, x_36);
x_37 = x_20;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
else
{
lean_del_object(x_11);
lean_dec_ref(x_9);
return x_18;
}
}
}
}
case 1:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; uint8_t x_189; uint8_t x_203; 
x_186 = lean_ctor_get(x_2, 0);
x_187 = lean_ctor_get(x_2, 1);
x_203 = !lean_is_exclusive(x_2);
if (x_203 == 0)
{
x_188 = x_2;
x_189 = x_203;
goto block_202;
}
else
{
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_2);
x_188 = lean_box(0);
x_189 = x_203;
goto block_202;
}
block_202:
{
lean_object* x_190; 
x_190 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_187, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_190) == 0)
{
lean_object* x_191; lean_object* x_192; uint8_t x_193; uint8_t x_201; 
x_191 = lean_ctor_get(x_190, 0);
x_201 = !lean_is_exclusive(x_190);
if (x_201 == 0)
{
x_192 = x_190;
x_193 = x_201;
goto block_200;
}
else
{
lean_inc(x_191);
lean_dec(x_190);
x_192 = lean_box(0);
x_193 = x_201;
goto block_200;
}
block_200:
{
lean_object* x_194; 
if (x_189 == 0)
{
lean_ctor_set(x_188, 1, x_191);
x_194 = x_188;
goto block_198;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_186);
lean_ctor_set(x_199, 1, x_191);
x_194 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_195; 
if (x_193 == 0)
{
lean_ctor_set(x_192, 0, x_194);
x_195 = x_192;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_197, 0, x_194);
x_195 = x_197;
goto block_196;
}
block_196:
{
return x_195;
}
}
}
}
else
{
lean_del_object(x_188);
lean_dec_ref(x_186);
return x_190;
}
}
}
case 2:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; uint8_t x_246; 
x_204 = lean_ctor_get(x_2, 0);
x_205 = lean_ctor_get(x_2, 1);
x_246 = !lean_is_exclusive(x_2);
if (x_246 == 0)
{
x_206 = x_2;
x_207 = x_246;
goto block_245;
}
else
{
lean_inc(x_205);
lean_inc(x_204);
lean_dec(x_2);
x_206 = lean_box(0);
x_207 = x_246;
goto block_245;
}
block_245:
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; 
x_208 = lean_ctor_get(x_204, 2);
lean_inc_ref(x_208);
x_209 = lean_ctor_get(x_204, 4);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc_ref(x_209);
x_210 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_209, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_210) == 0)
{
lean_object* x_211; uint8_t x_212; lean_object* x_213; 
x_211 = lean_ctor_get(x_210, 0);
lean_inc(x_211);
lean_dec_ref(x_210);
x_212 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_211);
lean_inc_ref(x_208);
x_213 = l_Lean_Compiler_LCNF_Code_inferParamType(x_212, x_208, x_211, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec_ref(x_213);
x_215 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_212, x_204, x_214, x_208, x_211, x_5);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
lean_dec_ref(x_215);
x_217 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_205, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; uint8_t x_220; uint8_t x_228; 
x_218 = lean_ctor_get(x_217, 0);
x_228 = !lean_is_exclusive(x_217);
if (x_228 == 0)
{
x_219 = x_217;
x_220 = x_228;
goto block_227;
}
else
{
lean_inc(x_218);
lean_dec(x_217);
x_219 = lean_box(0);
x_220 = x_228;
goto block_227;
}
block_227:
{
lean_object* x_221; 
if (x_207 == 0)
{
lean_ctor_set(x_206, 1, x_218);
lean_ctor_set(x_206, 0, x_216);
x_221 = x_206;
goto block_225;
}
else
{
lean_object* x_226; 
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_216);
lean_ctor_set(x_226, 1, x_218);
x_221 = x_226;
goto block_225;
}
block_225:
{
lean_object* x_222; 
if (x_220 == 0)
{
lean_ctor_set(x_219, 0, x_221);
x_222 = x_219;
goto block_223;
}
else
{
lean_object* x_224; 
x_224 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_224, 0, x_221);
x_222 = x_224;
goto block_223;
}
block_223:
{
return x_222;
}
}
}
}
else
{
lean_dec(x_216);
lean_del_object(x_206);
return x_217;
}
}
else
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_236; 
lean_del_object(x_206);
lean_dec_ref(x_205);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_229 = lean_ctor_get(x_215, 0);
x_236 = !lean_is_exclusive(x_215);
if (x_236 == 0)
{
x_230 = x_215;
x_231 = x_236;
goto block_235;
}
else
{
lean_inc(x_229);
lean_dec(x_215);
x_230 = lean_box(0);
x_231 = x_236;
goto block_235;
}
block_235:
{
lean_object* x_232; 
if (x_231 == 0)
{
x_232 = x_230;
goto block_233;
}
else
{
lean_object* x_234; 
x_234 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_234, 0, x_229);
x_232 = x_234;
goto block_233;
}
block_233:
{
return x_232;
}
}
}
}
else
{
lean_object* x_237; lean_object* x_238; uint8_t x_239; uint8_t x_244; 
lean_dec(x_211);
lean_dec_ref(x_208);
lean_del_object(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_237 = lean_ctor_get(x_213, 0);
x_244 = !lean_is_exclusive(x_213);
if (x_244 == 0)
{
x_238 = x_213;
x_239 = x_244;
goto block_243;
}
else
{
lean_inc(x_237);
lean_dec(x_213);
x_238 = lean_box(0);
x_239 = x_244;
goto block_243;
}
block_243:
{
lean_object* x_240; 
if (x_239 == 0)
{
x_240 = x_238;
goto block_241;
}
else
{
lean_object* x_242; 
x_242 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_242, 0, x_237);
x_240 = x_242;
goto block_241;
}
block_241:
{
return x_240;
}
}
}
}
else
{
lean_dec_ref(x_208);
lean_del_object(x_206);
lean_dec_ref(x_205);
lean_dec_ref(x_204);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_210;
}
}
}
case 4:
{
lean_object* x_247; lean_object* x_248; uint8_t x_249; uint8_t x_313; 
x_247 = lean_ctor_get(x_2, 0);
x_313 = !lean_is_exclusive(x_2);
if (x_313 == 0)
{
x_248 = x_2;
x_249 = x_313;
goto block_312;
}
else
{
lean_inc(x_247);
lean_dec(x_2);
x_248 = lean_box(0);
x_249 = x_313;
goto block_312;
}
block_312:
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; uint8_t x_310; 
x_250 = lean_ctor_get(x_247, 0);
x_251 = lean_ctor_get(x_247, 2);
x_252 = lean_ctor_get(x_247, 3);
x_310 = !lean_is_exclusive(x_247);
if (x_310 == 0)
{
lean_object* x_311; 
x_311 = lean_ctor_get(x_247, 1);
lean_dec(x_311);
x_253 = x_247;
x_254 = x_310;
goto block_309;
}
else
{
lean_inc(x_252);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_247);
x_253 = lean_box(0);
x_254 = x_310;
goto block_309;
}
block_309:
{
size_t x_255; size_t x_256; lean_object* x_257; 
x_255 = lean_array_size(x_252);
x_256 = 0;
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_257 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__4(x_1, x_255, x_256, x_252, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_257) == 0)
{
lean_object* x_258; uint8_t x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_288; lean_object* x_289; uint8_t x_290; 
x_258 = lean_ctor_get(x_257, 0);
lean_inc(x_258);
lean_dec_ref(x_257);
x_259 = 0;
x_288 = lean_array_get_size(x_258);
x_289 = lean_unsigned_to_nat(0u);
x_290 = lean_nat_dec_eq(x_288, x_289);
if (x_290 == 0)
{
x_260 = x_4;
x_261 = x_5;
x_262 = x_6;
x_263 = x_7;
goto block_287;
}
else
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__12);
x_292 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg(x_291, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_292) == 0)
{
lean_dec_ref(x_292);
x_260 = x_4;
x_261 = x_5;
x_262 = x_6;
x_263 = x_7;
goto block_287;
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; uint8_t x_300; 
lean_dec(x_258);
lean_del_object(x_253);
lean_dec(x_251);
lean_dec(x_250);
lean_del_object(x_248);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_293 = lean_ctor_get(x_292, 0);
x_300 = !lean_is_exclusive(x_292);
if (x_300 == 0)
{
x_294 = x_292;
x_295 = x_300;
goto block_299;
}
else
{
lean_inc(x_293);
lean_dec(x_292);
x_294 = lean_box(0);
x_295 = x_300;
goto block_299;
}
block_299:
{
lean_object* x_296; 
if (x_295 == 0)
{
x_296 = x_294;
goto block_297;
}
else
{
lean_object* x_298; 
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_293);
x_296 = x_298;
goto block_297;
}
block_297:
{
return x_296;
}
}
}
}
block_287:
{
lean_object* x_264; 
lean_inc(x_258);
x_264 = l_Lean_Compiler_LCNF_mkCasesResultType(x_259, x_258, x_260, x_261, x_262, x_263);
if (lean_obj_tag(x_264) == 0)
{
lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_278; 
x_265 = lean_ctor_get(x_264, 0);
x_278 = !lean_is_exclusive(x_264);
if (x_278 == 0)
{
x_266 = x_264;
x_267 = x_278;
goto block_277;
}
else
{
lean_inc(x_265);
lean_dec(x_264);
x_266 = lean_box(0);
x_267 = x_278;
goto block_277;
}
block_277:
{
lean_object* x_268; 
if (x_254 == 0)
{
lean_ctor_set(x_253, 3, x_258);
lean_ctor_set(x_253, 1, x_265);
x_268 = x_253;
goto block_275;
}
else
{
lean_object* x_276; 
x_276 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_276, 0, x_250);
lean_ctor_set(x_276, 1, x_265);
lean_ctor_set(x_276, 2, x_251);
lean_ctor_set(x_276, 3, x_258);
x_268 = x_276;
goto block_275;
}
block_275:
{
lean_object* x_269; 
if (x_249 == 0)
{
lean_ctor_set(x_248, 0, x_268);
x_269 = x_248;
goto block_273;
}
else
{
lean_object* x_274; 
x_274 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_274, 0, x_268);
x_269 = x_274;
goto block_273;
}
block_273:
{
lean_object* x_270; 
if (x_267 == 0)
{
lean_ctor_set(x_266, 0, x_269);
x_270 = x_266;
goto block_271;
}
else
{
lean_object* x_272; 
x_272 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_272, 0, x_269);
x_270 = x_272;
goto block_271;
}
block_271:
{
return x_270;
}
}
}
}
}
else
{
lean_object* x_279; lean_object* x_280; uint8_t x_281; uint8_t x_286; 
lean_dec(x_258);
lean_del_object(x_253);
lean_dec(x_251);
lean_dec(x_250);
lean_del_object(x_248);
x_279 = lean_ctor_get(x_264, 0);
x_286 = !lean_is_exclusive(x_264);
if (x_286 == 0)
{
x_280 = x_264;
x_281 = x_286;
goto block_285;
}
else
{
lean_inc(x_279);
lean_dec(x_264);
x_280 = lean_box(0);
x_281 = x_286;
goto block_285;
}
block_285:
{
lean_object* x_282; 
if (x_281 == 0)
{
x_282 = x_280;
goto block_283;
}
else
{
lean_object* x_284; 
x_284 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_284, 0, x_279);
x_282 = x_284;
goto block_283;
}
block_283:
{
return x_282;
}
}
}
}
}
else
{
lean_object* x_301; lean_object* x_302; uint8_t x_303; uint8_t x_308; 
lean_del_object(x_253);
lean_dec(x_251);
lean_dec(x_250);
lean_del_object(x_248);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_301 = lean_ctor_get(x_257, 0);
x_308 = !lean_is_exclusive(x_257);
if (x_308 == 0)
{
x_302 = x_257;
x_303 = x_308;
goto block_307;
}
else
{
lean_inc(x_301);
lean_dec(x_257);
x_302 = lean_box(0);
x_303 = x_308;
goto block_307;
}
block_307:
{
lean_object* x_304; 
if (x_303 == 0)
{
x_304 = x_302;
goto block_305;
}
else
{
lean_object* x_306; 
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_301);
x_304 = x_306;
goto block_305;
}
block_305:
{
return x_304;
}
}
}
}
}
}
case 5:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_314 = lean_ctor_get(x_2, 0);
lean_inc(x_314);
lean_dec_ref(x_2);
x_315 = lean_ctor_get(x_1, 0);
x_316 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_316, 0, x_314);
x_317 = lean_unsigned_to_nat(1u);
x_318 = lean_mk_empty_array_with_capacity(x_317);
x_319 = lean_array_push(x_318, x_316);
lean_inc(x_315);
x_320 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_320, 0, x_315);
lean_ctor_set(x_320, 1, x_319);
x_321 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_321, 0, x_320);
return x_321;
}
default: 
{
lean_object* x_322; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_322 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_322, 0, x_2);
return x_322;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_4);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_array_uget(x_4, x_3);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_uset(x_4, x_3, x_14);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_41; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
x_24 = lean_ctor_get(x_13, 2);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
x_25 = x_13;
x_26 = x_41;
goto block_40;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_25 = lean_box(0);
x_26 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_27; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_27 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_24, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec_ref(x_27);
if (x_26 == 0)
{
lean_ctor_set(x_25, 2, x_28);
x_29 = x_25;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_28);
x_29 = x_31;
goto block_30;
}
block_30:
{
x_16 = x_29;
goto block_21;
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_del_object(x_25);
lean_dec_ref(x_23);
lean_dec(x_22);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_32 = lean_ctor_get(x_27, 0);
x_39 = !lean_is_exclusive(x_27);
if (x_39 == 0)
{
x_33 = x_27;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_27);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_59; 
x_42 = lean_ctor_get(x_13, 0);
x_59 = !lean_is_exclusive(x_13);
if (x_59 == 0)
{
x_43 = x_13;
x_44 = x_59;
goto block_58;
}
else
{
lean_inc(x_42);
lean_dec(x_13);
x_43 = lean_box(0);
x_44 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_45; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_45 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_42, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
if (x_44 == 0)
{
lean_ctor_set(x_43, 0, x_46);
x_47 = x_43;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_46);
x_47 = x_49;
goto block_48;
}
block_48:
{
x_16 = x_47;
goto block_21;
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_57; 
lean_del_object(x_43);
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_50 = lean_ctor_get(x_45, 0);
x_57 = !lean_is_exclusive(x_45);
if (x_57 == 0)
{
x_51 = x_45;
x_52 = x_57;
goto block_56;
}
else
{
lean_inc(x_50);
lean_dec(x_45);
x_51 = lean_box(0);
x_52 = x_57;
goto block_56;
}
block_56:
{
lean_object* x_53; 
if (x_52 == 0)
{
x_53 = x_51;
goto block_54;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_50);
x_53 = x_55;
goto block_54;
}
block_54:
{
return x_53;
}
}
}
}
}
block_21:
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = 1;
x_18 = lean_usize_add(x_3, x_17);
x_19 = lean_array_uset(x_15, x_3, x_16);
x_3 = x_18;
x_4 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__4(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DTreeMap_Internal_Impl_erase___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__1(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___redArg(x_1, x_4, x_5, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__3(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__2(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__2_spec__3_spec__5_spec__8___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_29);
x_9 = x_29;
goto block_28;
}
case 1:
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_30);
x_9 = x_30;
goto block_28;
}
default: 
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_31);
x_9 = x_31;
goto block_28;
}
}
block_28:
{
lean_object* x_10; 
x_10 = lean_apply_7(x_2, x_9, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_19; 
x_11 = lean_ctor_get(x_10, 0);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
x_12 = x_10;
x_13 = x_19;
goto block_18;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp___redArg(x_1, x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_14);
x_15 = x_12;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_14);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec_ref(x_1);
x_20 = lean_ctor_get(x_10, 0);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
x_21 = x_10;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_3);
x_11 = lean_nat_dec_lt(x_2, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_fget_borrowed(x_3, x_2);
lean_inc_ref(x_1);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___boxed), 8, 1);
lean_closure_set(x_14, 0, x_1);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_13);
x_15 = l_Lean_Compiler_LCNF_Alt_mapCodeM___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__0___redArg(x_13, x_14, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; size_t x_17; size_t x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_ptr_addr(x_13);
x_18 = lean_ptr_addr(x_16);
x_19 = lean_usize_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_2, x_20);
x_22 = lean_array_fset(x_3, x_2, x_16);
lean_dec(x_2);
x_2 = x_21;
x_3 = x_22;
goto _start;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_16);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_2, x_24);
lean_dec(x_2);
x_2 = x_25;
goto _start;
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_27 = lean_ctor_get(x_15, 0);
x_34 = !lean_is_exclusive(x_15);
if (x_34 == 0)
{
x_28 = x_15;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_15);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts_spec__1(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_1, x_4);
lean_inc(x_3);
x_7 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_5;
goto _start;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_51; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get(x_2, 3);
x_51 = !lean_is_exclusive(x_2);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_2, 1);
lean_dec(x_52);
x_11 = x_2;
x_12 = x_51;
goto block_50;
}
else
{
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_2);
x_11 = lean_box(0);
x_12 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_box(1);
x_14 = lean_st_mk_ref(x_13);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
lean_inc(x_14);
lean_inc_ref(x_1);
x_15 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_visitAlts(x_1, x_10, x_14, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_st_ref_get(x_14);
lean_dec(x_14);
x_18 = 0;
lean_inc(x_16);
x_19 = l_Lean_Compiler_LCNF_mkCasesResultType(x_18, x_16, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_33; 
x_20 = lean_ctor_get(x_19, 0);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
x_21 = x_19;
x_22 = x_33;
goto block_32;
}
else
{
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_box(0);
x_22 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_23; 
if (x_12 == 0)
{
lean_ctor_set(x_11, 3, x_16);
lean_ctor_set(x_11, 1, x_20);
x_23 = x_11;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_9);
lean_ctor_set(x_31, 3, x_16);
x_23 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_24, x_17);
lean_dec(x_17);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
if (x_22 == 0)
{
lean_ctor_set(x_21, 0, x_26);
x_27 = x_21;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_17);
lean_dec(x_16);
lean_del_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec_ref(x_1);
x_34 = lean_ctor_get(x_19, 0);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
x_35 = x_19;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_19);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_49; 
lean_dec(x_14);
lean_del_object(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_42 = lean_ctor_get(x_15, 0);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
x_43 = x_15;
x_44 = x_49;
goto block_48;
}
else
{
lean_inc(x_42);
lean_dec(x_15);
x_43 = lean_box(0);
x_44 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_45; 
if (x_44 == 0)
{
x_45 = x_43;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_42);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_bindCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_bindCases(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Compiler_LCNF_ToLCNF_bindCases_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_2, x_3);
if (x_13 == 0)
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_20; 
x_14 = 0;
x_20 = lean_array_uget_borrowed(x_1, x_2);
switch (lean_obj_tag(x_20)) {
case 2:
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_20, 0);
x_22 = l_Lean_Compiler_LCNF_eraseLetDecl___redArg(x_14, x_21, x_5);
x_7 = x_22;
goto block_12;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc_ref(x_23);
x_24 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_14, x_24, x_5);
lean_dec_ref(x_24);
x_7 = x_25;
goto block_12;
}
case 4:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_14, x_26, x_5);
x_7 = x_27;
goto block_12;
}
default: 
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_28);
x_15 = x_28;
x_16 = x_5;
goto block_19;
}
}
block_19:
{
uint8_t x_17; lean_object* x_18; 
x_17 = 1;
x_18 = l_Lean_Compiler_LCNF_eraseFunDecl___redArg(x_14, x_15, x_17, x_16);
lean_dec_ref(x_15);
x_7 = x_18;
goto block_12;
}
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_4);
return x_29;
}
block_12:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec_ref(x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_8;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(x_1, x_7, x_8, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; uint8_t x_20; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_lt(x_19, x_2);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_3);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default;
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_2, x_23);
x_25 = lean_array_get(x_22, x_1, x_24);
switch (lean_obj_tag(x_25)) {
case 0:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_26 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_26);
lean_dec_ref(x_25);
x_27 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_3);
x_2 = x_24;
x_3 = x_27;
goto _start;
}
case 1:
{
lean_object* x_29; 
lean_dec(x_24);
x_29 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_29);
lean_dec_ref(x_25);
x_9 = x_29;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
goto block_18;
}
case 2:
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_30 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_30);
lean_dec_ref(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
x_2 = x_24;
x_3 = x_31;
goto _start;
}
case 3:
{
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_2);
x_33 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_33);
x_34 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_34);
lean_dec_ref(x_25);
x_35 = lean_ctor_get(x_3, 0);
x_36 = lean_ctor_get(x_33, 0);
x_37 = l_Lean_instBEqFVarId_beq(x_36, x_35);
if (x_37 == 0)
{
lean_dec_ref(x_34);
lean_dec_ref(x_33);
x_2 = x_24;
goto _start;
}
else
{
lean_object* x_39; uint8_t x_40; uint8_t x_56; 
x_56 = !lean_is_exclusive(x_3);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_3, 0);
lean_dec(x_57);
x_39 = x_3;
x_40 = x_56;
goto block_55;
}
else
{
lean_dec(x_3);
x_39 = lean_box(0);
x_40 = x_56;
goto block_55;
}
block_55:
{
uint8_t x_41; lean_object* x_42; 
x_41 = 0;
x_42 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_41, x_33, x_5);
lean_dec_ref(x_33);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; 
lean_dec_ref(x_42);
if (x_40 == 0)
{
lean_ctor_set_tag(x_39, 4);
lean_ctor_set(x_39, 0, x_34);
x_43 = x_39;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_46, 0, x_34);
x_43 = x_46;
goto block_45;
}
block_45:
{
x_2 = x_24;
x_3 = x_43;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_del_object(x_39);
lean_dec_ref(x_34);
lean_dec(x_24);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_47 = lean_ctor_get(x_42, 0);
x_54 = !lean_is_exclusive(x_42);
if (x_54 == 0)
{
x_48 = x_42;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_42);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_58 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_58);
x_59 = lean_ctor_get(x_25, 1);
lean_inc_ref(x_59);
lean_dec_ref(x_25);
x_60 = lean_ctor_get(x_58, 0);
x_61 = lean_ctor_get(x_58, 1);
x_62 = lean_ctor_get(x_58, 2);
lean_inc_ref(x_62);
x_63 = l_Lean_Expr_headBeta(x_62);
x_64 = l_Lean_Expr_isForall(x_63);
lean_dec_ref(x_63);
if (x_64 == 0)
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_2);
x_65 = 0;
x_66 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__10));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_67 = l_Lean_Compiler_LCNF_mkAuxJpDecl_x27(x_65, x_58, x_3, x_66, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
lean_dec_ref(x_67);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_69 = l_Lean_Compiler_LCNF_ToLCNF_bindCases(x_68, x_59, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_2 = x_24;
x_3 = x_70;
goto _start;
}
else
{
lean_dec(x_24);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
return x_69;
}
}
else
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; uint8_t x_79; 
lean_dec_ref(x_59);
lean_dec(x_24);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_1);
x_72 = lean_ctor_get(x_67, 0);
x_79 = !lean_is_exclusive(x_67);
if (x_79 == 0)
{
x_73 = x_67;
x_74 = x_79;
goto block_78;
}
else
{
lean_inc(x_72);
lean_dec(x_67);
x_73 = lean_box(0);
x_74 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_75; 
if (x_74 == 0)
{
x_75 = x_73;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_72);
x_75 = x_77;
goto block_76;
}
block_76:
{
return x_75;
}
}
}
}
else
{
uint8_t x_80; lean_object* x_81; 
lean_inc_ref(x_62);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_24);
x_80 = 0;
x_81 = l_Lean_Compiler_LCNF_eraseParam___redArg(x_80, x_58, x_5);
lean_dec_ref(x_58);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_106; 
lean_dec_ref(x_81);
x_82 = lean_st_ref_take(x_5);
x_83 = lean_ctor_get(x_82, 0);
x_84 = lean_ctor_get(x_82, 1);
x_106 = !lean_is_exclusive(x_82);
if (x_106 == 0)
{
x_85 = x_82;
x_86 = x_106;
goto block_105;
}
else
{
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_82);
x_85 = lean_box(0);
x_86 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_87 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_87, 0, x_59);
x_88 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__4));
x_89 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_89, 0, x_60);
lean_ctor_set(x_89, 1, x_61);
lean_ctor_set(x_89, 2, x_88);
lean_ctor_set(x_89, 3, x_62);
lean_ctor_set(x_89, 4, x_87);
lean_inc_ref(x_89);
x_90 = l_Lean_Compiler_LCNF_LCtx_addFunDecl(x_80, x_83, x_89);
if (x_86 == 0)
{
lean_ctor_set(x_85, 0, x_90);
x_91 = x_85;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_90);
lean_ctor_set(x_104, 1, x_84);
x_91 = x_104;
goto block_103;
}
block_103:
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_st_ref_set(x_5, x_91);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_93 = l_Lean_Compiler_LCNF_FunDecl_etaExpand(x_89, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
lean_dec_ref(x_93);
x_9 = x_94;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
goto block_18;
}
else
{
lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_102; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_95 = lean_ctor_get(x_93, 0);
x_102 = !lean_is_exclusive(x_93);
if (x_102 == 0)
{
x_96 = x_93;
x_97 = x_102;
goto block_101;
}
else
{
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
x_97 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_98; 
if (x_97 == 0)
{
x_98 = x_96;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_95);
x_98 = x_100;
goto block_99;
}
block_99:
{
return x_98;
}
}
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_107 = lean_ctor_get(x_81, 0);
x_114 = !lean_is_exclusive(x_81);
if (x_114 == 0)
{
x_108 = x_81;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_dec(x_81);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
}
}
}
default: 
{
lean_object* x_115; uint8_t x_116; uint8_t x_174; 
lean_dec(x_24);
x_174 = !lean_is_exclusive(x_25);
if (x_174 == 0)
{
lean_object* x_175; 
x_175 = lean_ctor_get(x_25, 0);
lean_dec(x_175);
x_115 = x_25;
x_116 = x_174;
goto block_173;
}
else
{
lean_dec(x_25);
x_115 = lean_box(0);
x_116 = x_174;
goto block_173;
}
block_173:
{
uint8_t x_117; lean_object* x_118; 
x_117 = 0;
lean_inc(x_5);
lean_inc_ref(x_3);
x_118 = l_Lean_Compiler_LCNF_Code_inferType(x_117, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; uint8_t x_164; 
x_119 = lean_ctor_get(x_118, 0);
x_164 = !lean_is_exclusive(x_118);
if (x_164 == 0)
{
x_120 = x_118;
x_121 = x_164;
goto block_163;
}
else
{
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_box(0);
x_121 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_129; lean_object* x_139; 
x_139 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_117, x_3, x_5);
lean_dec_ref(x_3);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
lean_dec_ref(x_139);
x_140 = l_Array_toSubarray___redArg(x_1, x_19, x_2);
x_141 = lean_ctor_get(x_140, 0);
lean_inc_ref(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 2);
lean_inc(x_143);
lean_dec_ref(x_140);
x_144 = lean_nat_dec_lt(x_142, x_143);
if (x_144 == 0)
{
lean_dec(x_143);
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_5);
goto block_128;
}
else
{
lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_145 = lean_box(0);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_143, x_146);
if (x_147 == 0)
{
uint8_t x_148; 
lean_dec(x_143);
x_148 = lean_nat_dec_lt(x_142, x_146);
if (x_148 == 0)
{
lean_dec(x_142);
lean_dec_ref(x_141);
lean_dec(x_5);
goto block_128;
}
else
{
size_t x_149; size_t x_150; lean_object* x_151; 
x_149 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_150 = lean_usize_of_nat(x_146);
x_151 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(x_141, x_149, x_150, x_145, x_5);
lean_dec(x_5);
lean_dec_ref(x_141);
x_129 = x_151;
goto block_138;
}
}
else
{
size_t x_152; size_t x_153; lean_object* x_154; 
x_152 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_153 = lean_usize_of_nat(x_143);
lean_dec(x_143);
x_154 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(x_141, x_152, x_153, x_145, x_5);
lean_dec(x_5);
lean_dec_ref(x_141);
x_129 = x_154;
goto block_138;
}
}
}
else
{
lean_object* x_155; lean_object* x_156; uint8_t x_157; uint8_t x_162; 
lean_del_object(x_120);
lean_dec(x_119);
lean_del_object(x_115);
lean_dec(x_5);
lean_dec(x_2);
lean_dec_ref(x_1);
x_155 = lean_ctor_get(x_139, 0);
x_162 = !lean_is_exclusive(x_139);
if (x_162 == 0)
{
x_156 = x_139;
x_157 = x_162;
goto block_161;
}
else
{
lean_inc(x_155);
lean_dec(x_139);
x_156 = lean_box(0);
x_157 = x_162;
goto block_161;
}
block_161:
{
lean_object* x_158; 
if (x_157 == 0)
{
x_158 = x_156;
goto block_159;
}
else
{
lean_object* x_160; 
x_160 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_160, 0, x_155);
x_158 = x_160;
goto block_159;
}
block_159:
{
return x_158;
}
}
}
block_128:
{
lean_object* x_122; 
if (x_116 == 0)
{
lean_ctor_set_tag(x_115, 6);
lean_ctor_set(x_115, 0, x_119);
x_122 = x_115;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_127, 0, x_119);
x_122 = x_127;
goto block_126;
}
block_126:
{
lean_object* x_123; 
if (x_121 == 0)
{
lean_ctor_set(x_120, 0, x_122);
x_123 = x_120;
goto block_124;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_125, 0, x_122);
x_123 = x_125;
goto block_124;
}
block_124:
{
return x_123;
}
}
}
block_138:
{
if (lean_obj_tag(x_129) == 0)
{
lean_dec_ref(x_129);
goto block_128;
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_137; 
lean_del_object(x_120);
lean_dec(x_119);
lean_del_object(x_115);
x_130 = lean_ctor_get(x_129, 0);
x_137 = !lean_is_exclusive(x_129);
if (x_137 == 0)
{
x_131 = x_129;
x_132 = x_137;
goto block_136;
}
else
{
lean_inc(x_130);
lean_dec(x_129);
x_131 = lean_box(0);
x_132 = x_137;
goto block_136;
}
block_136:
{
lean_object* x_133; 
if (x_132 == 0)
{
x_133 = x_131;
goto block_134;
}
else
{
lean_object* x_135; 
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_130);
x_133 = x_135;
goto block_134;
}
block_134:
{
return x_133;
}
}
}
}
}
}
else
{
lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_172; 
lean_del_object(x_115);
lean_dec(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
x_165 = lean_ctor_get(x_118, 0);
x_172 = !lean_is_exclusive(x_118);
if (x_172 == 0)
{
x_166 = x_118;
x_167 = x_172;
goto block_171;
}
else
{
lean_inc(x_165);
lean_dec(x_118);
x_166 = lean_box(0);
x_167 = x_172;
goto block_171;
}
block_171:
{
lean_object* x_168; 
if (x_167 == 0)
{
x_168 = x_166;
goto block_169;
}
else
{
lean_object* x_170; 
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_165);
x_168 = x_170;
goto block_169;
}
block_169:
{
return x_168;
}
}
}
}
}
}
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_2, x_14);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_3);
x_2 = x_15;
x_3 = x_16;
x_4 = x_10;
x_5 = x_11;
x_6 = x_12;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_3, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_1(x_4, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_apply_2(x_6, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_apply_1(x_5, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__3_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_7);
lean_dec_ref(x_1);
x_8 = lean_apply_1(x_3, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_9);
lean_dec_ref(x_1);
x_10 = lean_apply_1(x_4, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
lean_dec_ref(x_1);
x_12 = lean_apply_1(x_2, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
lean_dec_ref(x_1);
x_15 = lean_apply_2(x_5, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_16);
lean_dec_ref(x_1);
x_17 = lean_apply_1(x_6, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_4; lean_object* x_5; 
lean_dec(x_3);
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec_ref(x_1);
x_5 = lean_apply_1(x_2, x_4);
return x_5;
}
else
{
lean_object* x_6; 
lean_dec(x_2);
x_6 = lean_apply_2(x_3, x_1, lean_box(0));
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_5; lean_object* x_6; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec_ref(x_2);
x_6 = lean_apply_1(x_3, x_5);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_apply_2(x_4, x_2, lean_box(0));
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_array_get_size(x_1);
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_seqToCode_go(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_seqToCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1);
x_2 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4);
x_2 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__3);
x_3 = lean_box(1);
x_4 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1);
x_5 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_st_ref_get(x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_box(1);
x_9 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_10 = 0;
x_11 = lean_unsigned_to_nat(0u);
x_12 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_13 = lean_box(0);
x_14 = 1;
x_15 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_8);
lean_ctor_set(x_15, 2, x_7);
lean_ctor_set(x_15, 3, x_12);
lean_ctor_set(x_15, 4, x_13);
lean_ctor_set(x_15, 5, x_11);
lean_ctor_set(x_15, 6, x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*7 + 1, x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*7 + 2, x_10);
lean_ctor_set_uint8(x_15, sizeof(void*)*7 + 3, x_14);
x_16 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_17 = lean_st_mk_ref(x_16);
lean_inc(x_17);
x_18 = lean_apply_5(x_1, x_15, x_17, x_3, x_4, lean_box(0));
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_27; 
x_19 = lean_ctor_get(x_18, 0);
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
x_20 = x_18;
x_21 = x_27;
goto block_26;
}
else
{
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_st_ref_get(x_17);
lean_dec(x_17);
lean_dec(x_22);
if (x_21 == 0)
{
x_23 = x_20;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_19);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
else
{
lean_dec(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_st_ref_get(x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_box(1);
x_13 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_14 = 0;
x_15 = lean_unsigned_to_nat(0u);
x_16 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_17 = lean_box(0);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 1, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 2, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 3, x_18);
x_20 = lean_unsigned_to_nat(32u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec_ref(x_21);
x_22 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_23 = lean_st_mk_ref(x_22);
lean_inc(x_23);
x_24 = lean_apply_5(x_2, x_19, x_23, x_7, x_8, lean_box(0));
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_33; 
x_25 = lean_ctor_get(x_24, 0);
x_33 = !lean_is_exclusive(x_24);
if (x_33 == 0)
{
x_26 = x_24;
x_27 = x_33;
goto block_32;
}
else
{
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_st_ref_get(x_23);
lean_dec(x_23);
lean_dec(x_28);
if (x_27 == 0)
{
x_29 = x_26;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_25);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
else
{
lean_dec(x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_liftMetaM(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_22; 
x_4 = lean_st_ref_take(x_2);
x_5 = lean_ctor_get(x_4, 0);
x_6 = lean_ctor_get(x_4, 1);
x_7 = lean_ctor_get_uint8(x_4, sizeof(void*)*6);
x_8 = lean_ctor_get(x_4, 2);
x_9 = lean_ctor_get(x_4, 3);
x_10 = lean_ctor_get(x_4, 4);
x_11 = lean_ctor_get(x_4, 5);
x_22 = !lean_is_exclusive(x_4);
if (x_22 == 0)
{
x_12 = x_4;
x_13 = x_22;
goto block_21;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_4);
x_12 = lean_box(0);
x_13 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_push(x_10, x_1);
if (x_13 == 0)
{
lean_ctor_set(x_12, 4, x_14);
x_15 = x_12;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_8);
lean_ctor_set(x_20, 3, x_9);
lean_ctor_set(x_20, 4, x_14);
lean_ctor_set(x_20, 5, x_11);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_7);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_st_ref_set(x_2, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_pushElement___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_pushElement(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = 0;
x_9 = 0;
x_10 = l_Lean_Compiler_LCNF_mkAuxParam(x_8, x_1, x_9, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_22; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
lean_inc(x_11);
x_12 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_12, x_2);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_13, 0);
lean_dec(x_23);
x_14 = x_13;
x_15 = x_22;
goto block_21;
}
else
{
lean_dec(x_13);
x_14 = lean_box(0);
x_15 = x_22;
goto block_21;
}
block_21:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_17);
x_18 = x_14;
goto block_19;
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_17);
x_18 = x_20;
goto block_19;
}
block_19:
{
return x_18;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
x_24 = lean_ctor_get(x_10, 0);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
x_25 = x_10;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_10);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_1, 0);
x_58 = lean_ctor_get(x_1, 1);
x_59 = lean_array_get_size(x_58);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_nat_dec_eq(x_59, x_60);
if (x_61 == 0)
{
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
goto block_56;
}
else
{
lean_object* x_62; 
lean_inc(x_57);
lean_dec_ref(x_1);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_57);
return x_62;
}
}
else
{
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_7;
goto block_56;
}
block_56:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_2, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = 0;
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_1);
x_17 = l_Lean_Compiler_LCNF_LetValue_inferType(x_16, x_1, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Compiler_LCNF_mkLetDecl(x_16, x_15, x_18, x_1, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
lean_inc(x_20);
x_21 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_21, x_9);
x_30 = !lean_is_exclusive(x_22);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_22, 0);
lean_dec(x_31);
x_23 = x_22;
x_24 = x_30;
goto block_29;
}
else
{
lean_dec(x_22);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_20, 0);
lean_inc(x_25);
lean_dec(x_20);
if (x_24 == 0)
{
lean_ctor_set(x_23, 0, x_25);
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
x_32 = lean_ctor_get(x_19, 0);
x_39 = !lean_is_exclusive(x_19);
if (x_39 == 0)
{
x_33 = x_19;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_19);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_15);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_40 = lean_ctor_get(x_17, 0);
x_47 = !lean_is_exclusive(x_17);
if (x_47 == 0)
{
x_41 = x_17;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_17);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_1);
x_48 = lean_ctor_get(x_14, 0);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
x_49 = x_14;
x_50 = x_55;
goto block_54;
}
else
{
lean_inc(x_48);
lean_dec(x_14);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_18; 
x_10 = lean_ctor_get(x_9, 0);
x_18 = !lean_is_exclusive(x_9);
if (x_18 == 0)
{
x_11 = x_9;
x_12 = x_18;
goto block_17;
}
else
{
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = x_18;
goto block_17;
}
block_17:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_10);
if (x_12 == 0)
{
lean_ctor_set(x_11, 0, x_13);
x_14 = x_11;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_13);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
x_19 = lean_ctor_get(x_9, 0);
x_26 = !lean_is_exclusive(x_9);
if (x_26 == 0)
{
x_20 = x_9;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec_ref(x_1);
x_8 = x_19;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
goto block_18;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_20 = lean_box(1);
x_21 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_3);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg(x_20, x_21, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_8 = x_23;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
goto block_18;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = lean_ctor_get(x_22, 0);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
x_25 = x_22;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
block_18:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_st_ref_get(x_9);
x_15 = lean_ctor_get(x_14, 4);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_16, 0, x_8);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_seqToCode(x_15, x_16, x_10, x_11, x_12, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toCode___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toCode(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_unsigned_to_nat(32u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3(void) {
_start:
{
size_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 5;
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(32u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__2);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set_usize(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3);
x_3 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_mk_array(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__5);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_box(1);
x_2 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7));
x_3 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__6);
x_4 = 1;
x_5 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1);
x_6 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4);
x_7 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_3);
lean_ctor_set(x_7, 4, x_2);
lean_ctor_set(x_7, 5, x_1);
lean_ctor_set_uint8(x_7, sizeof(void*)*6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__8);
x_8 = lean_st_mk_ref(x_7);
x_9 = 0;
x_10 = lean_box(x_9);
lean_inc(x_8);
x_11 = lean_apply_7(x_1, x_10, x_8, x_2, x_3, x_4, x_5, lean_box(0));
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_20; 
x_12 = lean_ctor_get(x_11, 0);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
x_13 = x_11;
x_14 = x_20;
goto block_19;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_st_ref_get(x_8);
lean_dec(x_8);
lean_dec(x_15);
if (x_14 == 0)
{
x_16 = x_13;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_12);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_dec(x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg(x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_run___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_run(x_1, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 2);
x_2 = x_3;
goto _start;
}
case 10:
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_2, 1);
x_2 = x_5;
goto _start;
}
case 8:
{
uint8_t x_7; 
lean_dec_ref(x_1);
x_7 = 2;
return x_7;
}
case 3:
{
uint8_t x_8; 
lean_dec_ref(x_1);
x_8 = 1;
return x_8;
}
case 0:
{
uint8_t x_9; 
lean_dec_ref(x_1);
x_9 = 0;
return x_9;
}
default: 
{
lean_object* x_10; 
x_10 = l_Lean_Expr_getAppFn(x_2);
switch (lean_obj_tag(x_10)) {
case 0:
{
uint8_t x_11; 
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_11 = 0;
return x_11;
}
case 4:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec_ref(x_10);
x_13 = 0;
x_14 = l_Lean_Environment_find_x3f(x_1, x_12, x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
if (lean_obj_tag(x_15) == 5)
{
uint8_t x_16; 
lean_dec_ref(x_15);
x_16 = 0;
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_15);
x_17 = 2;
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_14);
x_18 = 2;
return x_18;
}
}
default: 
{
uint8_t x_19; 
lean_dec_ref(x_10);
lean_dec_ref(x_1);
x_19 = 2;
return x_19;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 0;
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_expr_eqv(x_4, x_1);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
return x_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_28; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 2);
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
x_6 = x_2;
x_7 = x_28;
goto block_27;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_8 = lean_array_get_size(x_1);
x_9 = l_Lean_Expr_hash(x_3);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_1, x_20);
lean_inc(x_21);
if (x_7 == 0)
{
lean_ctor_set(x_6, 2, x_21);
x_22 = x_6;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_4);
lean_ctor_set(x_26, 2, x_21);
x_22 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_23; 
x_23 = lean_array_uset(x_1, x_20, x_22);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
if (x_5 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2_spec__4___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_mul(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_18; 
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_3, 1);
x_6 = lean_ctor_get(x_3, 2);
x_18 = !lean_is_exclusive(x_3);
if (x_18 == 0)
{
x_7 = x_3;
x_8 = x_18;
goto block_17;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_9; 
x_9 = lean_expr_eqv(x_4, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__2___redArg(x_1, x_2, x_6);
if (x_8 == 0)
{
lean_ctor_set(x_7, 2, x_10);
x_11 = x_7;
goto block_12;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_13, 2, x_10);
x_11 = x_13;
goto block_12;
}
block_12:
{
return x_11;
}
}
else
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 0, x_1);
x_14 = x_7;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_6);
x_14 = x_16;
goto block_15;
}
block_15:
{
return x_14;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_48; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_48 = !lean_is_exclusive(x_1);
if (x_48 == 0)
{
x_6 = x_1;
x_7 = x_48;
goto block_47;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_48;
goto block_47;
}
block_47:
{
lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; uint8_t x_22; 
x_8 = lean_array_get_size(x_5);
x_9 = l_Lean_Expr_hash(x_2);
x_10 = 32;
x_11 = lean_uint64_shift_right(x_9, x_10);
x_12 = lean_uint64_xor(x_9, x_11);
x_13 = 16;
x_14 = lean_uint64_shift_right(x_12, x_13);
x_15 = lean_uint64_xor(x_12, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_8);
x_18 = 1;
x_19 = lean_usize_sub(x_17, x_18);
x_20 = lean_usize_land(x_16, x_19);
x_21 = lean_array_uget_borrowed(x_5, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___redArg(x_2, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_4, x_23);
lean_dec(x_4);
lean_inc(x_21);
x_25 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_25, 0, x_2);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_21);
x_26 = lean_array_uset(x_5, x_20, x_25);
x_27 = lean_unsigned_to_nat(4u);
x_28 = lean_nat_mul(x_24, x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = lean_nat_div(x_28, x_29);
lean_dec(x_28);
x_31 = lean_array_get_size(x_26);
x_32 = lean_nat_dec_le(x_30, x_31);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1___redArg(x_26);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_33);
lean_ctor_set(x_6, 0, x_24);
x_34 = x_6;
goto block_35;
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_33);
x_34 = x_36;
goto block_35;
}
block_35:
{
return x_34;
}
}
else
{
lean_object* x_37; 
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_26);
lean_ctor_set(x_6, 0, x_24);
x_37 = x_6;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_24);
lean_ctor_set(x_39, 1, x_26);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_21);
x_40 = lean_box(0);
x_41 = lean_array_uset(x_5, x_20, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__2___redArg(x_2, x_3, x_21);
x_43 = lean_array_uset(x_41, x_20, x_42);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_43);
x_44 = x_6;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_4);
lean_ctor_set(x_46, 1, x_43);
x_44 = x_46;
goto block_45;
}
block_45:
{
return x_44;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_expr_eqv(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
x_5 = l_Lean_Expr_hash(x_2);
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___redArg(x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_6; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_st_ref_get(x_4);
x_29 = lean_ctor_get(x_28, 0);
lean_inc_ref(x_29);
lean_dec(x_28);
x_30 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_quick(x_29, x_1);
switch (x_30) {
case 0:
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_31 = 0;
x_32 = lean_box(x_31);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_32);
return x_33;
}
case 1:
{
uint8_t x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_34 = 1;
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
default: 
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_st_ref_get(x_2);
x_38 = lean_ctor_get(x_37, 3);
lean_inc_ref(x_38);
lean_dec(x_37);
x_39 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_38, x_1);
lean_dec_ref(x_38);
if (lean_obj_tag(x_39) == 1)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_40 = lean_ctor_get(x_39, 0);
x_47 = !lean_is_exclusive(x_39);
if (x_47 == 0)
{
x_41 = x_39;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
lean_ctor_set_tag(x_41, 0);
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_39);
x_48 = lean_st_ref_get(x_2);
x_49 = lean_ctor_get(x_48, 0);
lean_inc_ref(x_49);
lean_dec(x_48);
x_50 = lean_box(1);
x_51 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_52 = 0;
x_53 = lean_unsigned_to_nat(0u);
x_54 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_55 = lean_box(0);
x_56 = 1;
x_57 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_57, 0, x_51);
lean_ctor_set(x_57, 1, x_50);
lean_ctor_set(x_57, 2, x_49);
lean_ctor_set(x_57, 3, x_54);
lean_ctor_set(x_57, 4, x_55);
lean_ctor_set(x_57, 5, x_53);
lean_ctor_set(x_57, 6, x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*7, x_52);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 1, x_52);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 2, x_52);
lean_ctor_set_uint8(x_57, sizeof(void*)*7 + 3, x_56);
x_58 = lean_unsigned_to_nat(32u);
x_59 = lean_mk_empty_array_with_capacity(x_58);
lean_dec_ref(x_59);
x_60 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_61 = lean_st_mk_ref(x_60);
lean_inc(x_61);
lean_inc_ref(x_1);
x_62 = l_Lean_Meta_isTypeFormerType(x_1, x_57, x_61, x_3, x_4);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
lean_dec_ref(x_62);
x_64 = lean_st_ref_get(x_61);
lean_dec(x_61);
lean_dec(x_64);
x_65 = lean_unbox(x_63);
lean_dec(x_63);
x_6 = x_65;
goto block_27;
}
else
{
lean_dec(x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec_ref(x_62);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
x_6 = x_67;
goto block_27;
}
else
{
lean_dec_ref(x_1);
return x_62;
}
}
}
}
}
block_27:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_26; 
x_7 = lean_st_ref_take(x_2);
x_8 = lean_ctor_get(x_7, 0);
x_9 = lean_ctor_get(x_7, 1);
x_10 = lean_ctor_get_uint8(x_7, sizeof(void*)*6);
x_11 = lean_ctor_get(x_7, 2);
x_12 = lean_ctor_get(x_7, 3);
x_13 = lean_ctor_get(x_7, 4);
x_14 = lean_ctor_get(x_7, 5);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
x_15 = x_7;
x_16 = x_26;
goto block_25;
}
else
{
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_7);
x_15 = lean_box(0);
x_16 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_box(x_6);
x_18 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_12, x_1, x_17);
if (x_16 == 0)
{
lean_ctor_set(x_15, 3, x_18);
x_19 = x_15;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_9);
lean_ctor_set(x_24, 2, x_11);
lean_ctor_set(x_24, 3, x_18);
lean_ctor_set(x_24, 4, x_13);
lean_ctor_set(x_24, 5, x_14);
lean_ctor_set_uint8(x_24, sizeof(void*)*6, x_10);
x_19 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_st_ref_set(x_2, x_19);
x_21 = lean_box(x_6);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_1, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1_spec__4(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0_spec__1_spec__2_spec__4___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
x_9 = lean_st_ref_get(x_1);
x_10 = lean_st_ref_get(x_1);
x_11 = lean_ctor_get(x_9, 2);
lean_inc_ref(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 3);
x_21 = !lean_is_exclusive(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_10, 5);
lean_dec(x_22);
x_23 = lean_ctor_get(x_10, 4);
lean_dec(x_23);
x_24 = lean_ctor_get(x_10, 2);
lean_dec(x_24);
x_25 = lean_ctor_get(x_10, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_10, 0);
lean_dec(x_26);
x_13 = x_10;
x_14 = x_21;
goto block_20;
}
else
{
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_15; 
if (x_14 == 0)
{
lean_ctor_set(x_13, 5, x_6);
lean_ctor_set(x_13, 4, x_5);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 1, x_3);
lean_ctor_set(x_13, 0, x_2);
x_15 = x_13;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_3);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_5);
lean_ctor_set(x_19, 5, x_6);
x_15 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
lean_ctor_set_uint8(x_15, sizeof(void*)*6, x_4);
x_16 = lean_st_ref_set(x_1, x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_4);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_1, x_2, x_3, x_9, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_60; 
x_9 = lean_st_ref_get(x_3);
x_10 = lean_st_ref_take(x_3);
x_11 = lean_ctor_get(x_10, 0);
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
x_14 = lean_ctor_get(x_10, 2);
x_15 = lean_ctor_get(x_10, 3);
x_16 = lean_ctor_get(x_10, 5);
x_60 = !lean_is_exclusive(x_10);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = lean_ctor_get(x_10, 4);
lean_dec(x_61);
x_17 = x_10;
x_18 = x_60;
goto block_59;
}
else
{
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_19; lean_object* x_20; 
x_19 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__7));
if (x_18 == 0)
{
lean_ctor_set(x_17, 4, x_19);
x_20 = x_17;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_58, 0, x_11);
lean_ctor_set(x_58, 1, x_12);
lean_ctor_set(x_58, 2, x_14);
lean_ctor_set(x_58, 3, x_15);
lean_ctor_set(x_58, 4, x_19);
lean_ctor_set(x_58, 5, x_16);
lean_ctor_set_uint8(x_58, sizeof(void*)*6, x_13);
x_20 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_st_ref_set(x_3, x_20);
x_22 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_22);
x_23 = lean_ctor_get(x_9, 1);
lean_inc_ref(x_23);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*6);
x_25 = lean_ctor_get(x_9, 4);
lean_inc_ref(x_25);
x_26 = lean_ctor_get(x_9, 5);
lean_inc(x_26);
lean_dec(x_9);
x_27 = lean_box(x_2);
lean_inc(x_3);
x_28 = lean_apply_7(x_1, x_27, x_3, x_4, x_5, x_6, x_7, lean_box(0));
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_45; 
x_29 = lean_ctor_get(x_28, 0);
x_45 = !lean_is_exclusive(x_28);
if (x_45 == 0)
{
x_30 = x_28;
x_31 = x_45;
goto block_44;
}
else
{
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_box(0);
x_31 = x_45;
goto block_44;
}
block_44:
{
lean_object* x_32; 
lean_inc(x_29);
if (x_31 == 0)
{
lean_ctor_set_tag(x_30, 1);
x_32 = x_30;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_29);
x_32 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_40; 
x_33 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_3, x_22, x_23, x_24, x_25, x_26, x_32);
lean_dec_ref(x_32);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_33);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_33, 0);
lean_dec(x_41);
x_34 = x_33;
x_35 = x_40;
goto block_39;
}
else
{
lean_dec(x_33);
x_34 = lean_box(0);
x_35 = x_40;
goto block_39;
}
block_39:
{
lean_object* x_36; 
if (x_35 == 0)
{
lean_ctor_set(x_34, 0, x_29);
x_36 = x_34;
goto block_37;
}
else
{
lean_object* x_38; 
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_29);
x_36 = x_38;
goto block_37;
}
block_37:
{
return x_36;
}
}
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_55; 
x_46 = lean_ctor_get(x_28, 0);
lean_inc(x_46);
lean_dec_ref(x_28);
x_47 = lean_box(0);
x_48 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___lam__0(x_3, x_22, x_23, x_24, x_25, x_26, x_47);
lean_dec(x_3);
x_55 = !lean_is_exclusive(x_48);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_48, 0);
lean_dec(x_56);
x_49 = x_48;
x_50 = x_55;
goto block_54;
}
else
{
lean_dec(x_48);
x_49 = lean_box(0);
x_50 = x_55;
goto block_54;
}
block_54:
{
lean_object* x_51; 
if (x_50 == 0)
{
lean_ctor_set_tag(x_49, 1);
lean_ctor_set(x_49, 0, x_46);
x_51 = x_49;
goto block_52;
}
else
{
lean_object* x_53; 
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_46);
x_51 = x_53;
goto block_52;
}
block_52:
{
return x_51;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_withNewScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 3);
x_5 = lean_ctor_get(x_2, 4);
x_6 = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(x_1, x_3);
switch (x_6) {
case 0:
{
x_2 = x_4;
goto _start;
}
case 1:
{
uint8_t x_8; 
x_8 = 1;
return x_8;
}
default: 
{
x_2 = x_5;
goto _start;
}
}
}
else
{
uint8_t x_10; 
x_10 = 0;
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_Compiler_LCNF_anyExpr;
x_2 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0, &l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0_once, _init_l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___closed__0);
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0(x_1, x_2);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 5);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_6, 0, x_5);
x_7 = lean_replace_expr(x_6, x_1);
lean_dec_ref(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_1, x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_applyToAny___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_st_ref_get(x_2);
x_35 = lean_ctor_get(x_34, 2);
lean_inc_ref(x_35);
lean_dec(x_34);
x_36 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__1___redArg(x_35, x_1);
lean_dec_ref(x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_37 = lean_st_ref_get(x_2);
x_38 = lean_ctor_get(x_37, 0);
lean_inc_ref(x_38);
lean_dec(x_37);
x_39 = lean_box(1);
x_40 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_41 = 0;
x_42 = lean_unsigned_to_nat(0u);
x_43 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_44 = lean_box(0);
x_45 = 1;
x_46 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_39);
lean_ctor_set(x_46, 2, x_38);
lean_ctor_set(x_46, 3, x_43);
lean_ctor_set(x_46, 4, x_44);
lean_ctor_set(x_46, 5, x_42);
lean_ctor_set(x_46, 6, x_44);
lean_ctor_set_uint8(x_46, sizeof(void*)*7, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 1, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 2, x_41);
lean_ctor_set_uint8(x_46, sizeof(void*)*7 + 3, x_45);
x_47 = lean_unsigned_to_nat(32u);
x_48 = lean_mk_empty_array_with_capacity(x_47);
lean_dec_ref(x_48);
x_49 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_50 = lean_st_mk_ref(x_49);
lean_inc(x_50);
lean_inc_ref(x_1);
x_51 = l_Lean_Compiler_LCNF_toLCNFType(x_1, x_46, x_50, x_3, x_4);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
lean_dec_ref(x_51);
x_53 = lean_st_ref_get(x_50);
lean_dec(x_50);
lean_dec(x_53);
x_6 = x_52;
goto block_33;
}
else
{
lean_dec(x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_51, 0);
lean_inc(x_54);
lean_dec_ref(x_51);
x_6 = x_54;
goto block_33;
}
else
{
lean_dec_ref(x_1);
return x_51;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_55 = lean_ctor_get(x_36, 0);
x_62 = !lean_is_exclusive(x_36);
if (x_62 == 0)
{
x_56 = x_36;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_36);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
lean_ctor_set_tag(x_56, 0);
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
block_33:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_32; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_6, x_2);
lean_dec_ref(x_6);
x_8 = lean_ctor_get(x_7, 0);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
x_9 = x_7;
x_10 = x_32;
goto block_31;
}
else
{
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_30; 
x_11 = lean_st_ref_take(x_2);
x_12 = lean_ctor_get(x_11, 0);
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get_uint8(x_11, sizeof(void*)*6);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_18 = lean_ctor_get(x_11, 5);
x_30 = !lean_is_exclusive(x_11);
if (x_30 == 0)
{
x_19 = x_11;
x_20 = x_30;
goto block_29;
}
else
{
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_11);
x_19 = lean_box(0);
x_20 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_8);
x_21 = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType_spec__0___redArg(x_15, x_1, x_8);
if (x_20 == 0)
{
lean_ctor_set(x_19, 2, x_21);
x_22 = x_19;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_28, 0, x_12);
lean_ctor_set(x_28, 1, x_13);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_16);
lean_ctor_set(x_28, 4, x_17);
lean_ctor_set(x_28, 5, x_18);
lean_ctor_set_uint8(x_28, sizeof(void*)*6, x_14);
x_22 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_st_ref_set(x_2, x_22);
if (x_10 == 0)
{
x_24 = x_9;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_8);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_3, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Name_hasMacroScopes(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_1);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_erase_macro_scopes(x_1);
x_7 = l_Lean_Compiler_LCNF_mkFreshBinderName___redArg(x_6, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_isMarkedBorrowed(x_2);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_2, x_3, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_14 = 0;
lean_inc(x_10);
x_15 = l_Lean_Compiler_LCNF_mkParam(x_14, x_10, x_13, x_11, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_43; 
x_16 = lean_ctor_get(x_15, 0);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
x_17 = x_15;
x_18 = x_43;
goto block_42;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_41; 
x_19 = lean_st_ref_take(x_3);
x_20 = lean_ctor_get(x_19, 0);
x_21 = lean_ctor_get(x_19, 1);
x_22 = lean_ctor_get_uint8(x_19, sizeof(void*)*6);
x_23 = lean_ctor_get(x_19, 2);
x_24 = lean_ctor_get(x_19, 3);
x_25 = lean_ctor_get(x_19, 4);
x_26 = lean_ctor_get(x_19, 5);
x_41 = !lean_is_exclusive(x_19);
if (x_41 == 0)
{
x_27 = x_19;
x_28 = x_41;
goto block_40;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_19);
x_27 = lean_box(0);
x_28 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_16, 0);
x_30 = 0;
x_31 = 0;
lean_inc(x_29);
x_32 = l_Lean_LocalContext_mkLocalDecl(x_20, x_29, x_10, x_2, x_30, x_31);
if (x_28 == 0)
{
lean_ctor_set(x_27, 0, x_32);
x_33 = x_27;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_21);
lean_ctor_set(x_39, 2, x_23);
lean_ctor_set(x_39, 3, x_24);
lean_ctor_set(x_39, 4, x_25);
lean_ctor_set(x_39, 5, x_26);
lean_ctor_set_uint8(x_39, sizeof(void*)*6, x_22);
x_33 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_st_ref_set(x_3, x_33);
if (x_18 == 0)
{
x_35 = x_17;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_16);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
else
{
lean_dec(x_10);
lean_dec_ref(x_2);
return x_15;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_44 = lean_ctor_get(x_12, 0);
x_51 = !lean_is_exclusive(x_12);
if (x_51 == 0)
{
x_45 = x_12;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_12);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_52 = lean_ctor_get(x_9, 0);
x_59 = !lean_is_exclusive(x_9);
if (x_59 == 0)
{
x_53 = x_9;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_mkParam___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_mkParam___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_mkParam(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_cleanupBinderName___redArg(x_1, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_5) == 1)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_5, 0);
x_54 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg___closed__0));
lean_inc(x_53);
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_14 = x_55;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
goto block_52;
}
else
{
lean_object* x_56; 
x_56 = lean_box(1);
x_14 = x_56;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
x_19 = x_10;
goto block_52;
}
block_52:
{
uint8_t x_20; lean_object* x_21; 
x_20 = 0;
lean_inc(x_13);
x_21 = l_Lean_Compiler_LCNF_mkLetDecl(x_20, x_13, x_4, x_14, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_51; 
x_22 = lean_ctor_get(x_21, 0);
x_51 = !lean_is_exclusive(x_21);
if (x_51 == 0)
{
x_23 = x_21;
x_24 = x_51;
goto block_50;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_49; 
x_25 = lean_st_ref_take(x_15);
x_26 = lean_ctor_get(x_25, 0);
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get_uint8(x_25, sizeof(void*)*6);
x_29 = lean_ctor_get(x_25, 2);
x_30 = lean_ctor_get(x_25, 3);
x_31 = lean_ctor_get(x_25, 4);
x_32 = lean_ctor_get(x_25, 5);
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
x_33 = x_25;
x_34 = x_49;
goto block_48;
}
else
{
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_25);
x_33 = lean_box(0);
x_34 = x_49;
goto block_48;
}
block_48:
{
lean_object* x_35; uint8_t x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_22, 0);
x_36 = 0;
x_37 = 0;
lean_inc(x_35);
x_38 = l_Lean_LocalContext_mkLetDecl(x_26, x_35, x_13, x_2, x_3, x_36, x_37);
lean_inc(x_22);
x_39 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_39, 0, x_22);
x_40 = lean_array_push(x_31, x_39);
if (x_34 == 0)
{
lean_ctor_set(x_33, 4, x_40);
lean_ctor_set(x_33, 0, x_38);
x_41 = x_33;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_47, 0, x_38);
lean_ctor_set(x_47, 1, x_27);
lean_ctor_set(x_47, 2, x_29);
lean_ctor_set(x_47, 3, x_30);
lean_ctor_set(x_47, 4, x_40);
lean_ctor_set(x_47, 5, x_32);
lean_ctor_set_uint8(x_47, sizeof(void*)*6, x_28);
x_41 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_st_ref_set(x_15, x_41);
if (x_24 == 0)
{
x_43 = x_23;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_22);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
else
{
lean_dec(x_13);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_21;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_57 = lean_ctor_get(x_12, 0);
x_64 = !lean_is_exclusive(x_12);
if (x_64 == 0)
{
x_58 = x_12;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_12);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec_ref(x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkParam___redArg(x_10, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_15);
x_16 = l_Lean_Compiler_LCNF_Param_toExpr___redArg(x_15);
x_17 = lean_array_push(x_2, x_16);
x_18 = lean_array_push(x_3, x_15);
x_1 = x_12;
x_2 = x_17;
x_3 = x_18;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec_ref(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_20 = lean_ctor_get(x_14, 0);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
x_21 = x_14;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_8);
lean_dec_ref(x_7);
x_28 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_3);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg___closed__0));
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitLambda_go___redArg(x_1, x_8, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 0)
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_15);
lean_dec_ref(x_1);
x_16 = lean_expr_instantiate_rev(x_14, x_3);
lean_dec_ref(x_14);
lean_inc(x_9);
lean_inc_ref(x_8);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_mkParam___redArg(x_13, x_16, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_2, x_19);
lean_dec(x_2);
lean_inc(x_18);
x_21 = l_Lean_Compiler_LCNF_Param_toExpr___redArg(x_18);
x_22 = lean_array_push(x_3, x_21);
x_23 = lean_array_push(x_4, x_18);
x_1 = x_15;
x_2 = x_20;
x_3 = x_22;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_32; 
lean_dec_ref(x_15);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_25 = lean_ctor_get(x_17, 0);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_26 = x_17;
x_27 = x_32;
goto block_31;
}
else
{
lean_inc(x_25);
lean_dec(x_17);
x_26 = lean_box(0);
x_27 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_28; 
if (x_27 == 0)
{
x_28 = x_26;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_25);
x_28 = x_30;
goto block_29;
}
block_29:
{
return x_28;
}
}
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
x_33 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_2);
x_36 = lean_expr_instantiate_rev(x_1, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_4);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
return x_38;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg___closed__0));
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda_go___redArg(x_1, x_2, x_9, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; uint8_t x_5; uint8_t x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec_ref(x_3);
x_13 = 0;
lean_inc(x_4);
lean_inc_ref(x_1);
x_14 = l_Lean_Environment_find_x3f(x_1, x_4, x_13);
if (lean_obj_tag(x_14) == 1)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
switch (lean_obj_tag(x_15)) {
case 7:
{
uint8_t x_16; 
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec_ref(x_1);
x_16 = 1;
return x_16;
}
case 6:
{
uint8_t x_17; 
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec_ref(x_1);
x_17 = 1;
return x_17;
}
case 4:
{
uint8_t x_18; 
lean_dec_ref(x_15);
lean_dec(x_4);
lean_dec_ref(x_1);
x_18 = 1;
return x_18;
}
default: 
{
lean_dec(x_15);
goto block_12;
}
}
}
else
{
lean_dec(x_14);
goto block_12;
}
block_9:
{
if (x_5 == 0)
{
uint8_t x_6; 
lean_inc(x_4);
x_6 = l_Lean_Environment_isProjectionFn(x_1, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2));
x_8 = lean_name_eq(x_4, x_7);
lean_dec(x_4);
return x_8;
}
else
{
lean_dec(x_4);
return x_6;
}
}
else
{
lean_dec(x_4);
lean_dec_ref(x_1);
return x_5;
}
}
block_12:
{
uint8_t x_10; 
lean_inc(x_4);
lean_inc_ref(x_1);
x_10 = l_Lean_isCasesOnLike(x_1, x_4);
if (x_10 == 0)
{
uint8_t x_11; 
lean_inc(x_4);
lean_inc_ref(x_1);
x_11 = l_Lean_isNoConfusion(x_1, x_4);
x_5 = x_11;
goto block_9;
}
else
{
x_5 = x_10;
goto block_9;
}
}
}
else
{
uint8_t x_19; 
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_19 = 0;
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_11, 0, x_3);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAux(lean_box(0), x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
x_14 = x_12;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
x_12 = lean_unbox(x_5);
x_13 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_5);
x_13 = lean_unbox(x_6);
x_14 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0(x_1, x_2, x_3, x_4, x_12, x_13, x_7, x_8, x_9, x_10);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = l_Lean_mkAppN(x_1, x_4);
x_12 = 1;
x_13 = l_Lean_Meta_mkLambdaFVars(x_4, x_11, x_2, x_3, x_2, x_3, x_12, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
x_12 = lean_unbox(x_3);
x_13 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_32; 
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_box(1);
x_12 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_13 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_14 = lean_box(0);
x_15 = 1;
x_16 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set(x_16, 4, x_14);
lean_ctor_set(x_16, 5, x_7);
lean_ctor_set(x_16, 6, x_14);
lean_ctor_set_uint8(x_16, sizeof(void*)*7, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*7 + 1, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*7 + 2, x_8);
lean_ctor_set_uint8(x_16, sizeof(void*)*7 + 3, x_15);
x_17 = lean_unsigned_to_nat(32u);
x_18 = lean_mk_empty_array_with_capacity(x_17);
lean_dec_ref(x_18);
x_19 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_20 = lean_st_mk_ref(x_19);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_20);
lean_inc_ref(x_16);
lean_inc_ref(x_1);
x_32 = lean_infer_type(x_1, x_16, x_20, x_4, x_5);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_44; 
x_33 = lean_ctor_get(x_32, 0);
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
x_34 = x_32;
x_35 = x_44;
goto block_43;
}
else
{
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_box(0);
x_35 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_36 = lean_box(x_8);
x_37 = lean_box(x_15);
x_38 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___lam__0___boxed), 10, 3);
lean_closure_set(x_38, 0, x_1);
lean_closure_set(x_38, 1, x_36);
lean_closure_set(x_38, 2, x_37);
if (x_35 == 0)
{
lean_ctor_set_tag(x_34, 1);
lean_ctor_set(x_34, 0, x_2);
x_39 = x_34;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_2);
x_39 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_40; 
lean_inc(x_20);
x_40 = l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg(x_33, x_39, x_38, x_8, x_8, x_16, x_20, x_4, x_5);
x_21 = x_40;
goto block_31;
}
}
}
else
{
lean_dec_ref(x_16);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
lean_dec_ref(x_1);
x_21 = x_32;
goto block_31;
}
block_31:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_30; 
x_22 = lean_ctor_get(x_21, 0);
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
x_23 = x_21;
x_24 = x_30;
goto block_29;
}
else
{
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_st_ref_get(x_20);
lean_dec(x_20);
lean_dec(x_25);
if (x_24 == 0)
{
x_26 = x_23;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_22);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
else
{
lean_dec(x_20);
return x_21;
}
}
}
else
{
lean_object* x_45; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_1);
return x_45;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_2, x_4, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_5, 2);
x_9 = lean_ctor_get(x_5, 5);
x_10 = lean_st_ref_get(x_6);
x_11 = lean_st_ref_get(x_4);
x_12 = l_Lean_Compiler_LCNF_getPurity___redArg(x_3);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_36; 
x_13 = lean_ctor_get(x_12, 0);
x_36 = !lean_is_exclusive(x_12);
if (x_36 == 0)
{
x_14 = x_12;
x_15 = x_36;
goto block_35;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_33; 
x_16 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_16);
lean_dec(x_10);
x_17 = lean_ctor_get(x_11, 0);
x_33 = !lean_is_exclusive(x_11);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_11, 1);
lean_dec(x_34);
x_18 = x_11;
x_19 = x_33;
goto block_32;
}
else
{
lean_inc(x_17);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = l_Lean_MessageData_tagWithErrorName(x_2, x_1);
x_21 = lean_unbox(x_13);
lean_dec(x_13);
x_22 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_17, x_21);
lean_dec_ref(x_17);
x_23 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2);
lean_inc_ref(x_8);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_16);
lean_ctor_set(x_24, 1, x_23);
lean_ctor_set(x_24, 2, x_22);
lean_ctor_set(x_24, 3, x_8);
if (x_19 == 0)
{
lean_ctor_set_tag(x_18, 3);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_25 = x_18;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_31, 0, x_24);
lean_ctor_set(x_31, 1, x_20);
x_25 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_26; lean_object* x_27; 
lean_inc(x_9);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
if (x_15 == 0)
{
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_26);
x_27 = x_14;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_26);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
x_37 = lean_ctor_get(x_12, 0);
x_44 = !lean_is_exclusive(x_12);
if (x_44 == 0)
{
x_38 = x_12;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_12);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___redArg(x_2, x_3, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
return x_12;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_9; uint8_t x_20; 
if (x_2 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_24 = lean_st_ref_get(x_7);
x_25 = lean_st_ref_get(x_7);
x_29 = lean_ctor_get(x_24, 0);
lean_inc_ref(x_29);
lean_dec(x_24);
x_30 = lean_ctor_get(x_25, 0);
lean_inc_ref(x_30);
lean_dec(x_25);
x_31 = 1;
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_53) == 1)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_1, 1);
x_56 = lean_ctor_get(x_53, 1);
x_57 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__11));
x_58 = lean_string_dec_eq(x_56, x_57);
if (x_58 == 0)
{
goto block_52;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__12));
x_60 = lean_string_dec_eq(x_55, x_59);
if (x_60 == 0)
{
lean_object* x_61; uint8_t x_62; 
x_61 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__13));
x_62 = lean_string_dec_eq(x_55, x_61);
if (x_62 == 0)
{
goto block_52;
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
goto block_28;
}
}
else
{
lean_dec_ref(x_1);
lean_dec_ref(x_30);
lean_dec_ref(x_29);
goto block_28;
}
}
}
else
{
goto block_52;
}
}
else
{
goto block_52;
}
}
else
{
goto block_52;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
block_52:
{
uint8_t x_32; 
lean_inc(x_1);
x_32 = l_Lean_isExtern(x_29, x_1);
if (x_32 == 0)
{
lean_object* x_33; 
lean_inc(x_1);
x_33 = l_Lean_Compiler_getImplementedBy_x3f(x_30, x_1);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_34 = lean_st_ref_get(x_7);
x_35 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_35);
lean_dec(x_34);
x_36 = l_Lean_noncomputableExt;
x_37 = lean_ctor_get(x_36, 0);
lean_inc_ref(x_37);
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_1);
x_39 = l_Lean_isNoncomputable(x_35, x_1, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_st_ref_get(x_7);
x_41 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_41);
lean_dec(x_40);
lean_inc(x_1);
x_42 = l_Lean_getOriginalConstKind_x3f(x_41, x_1);
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec_ref(x_42);
x_44 = lean_unbox(x_43);
lean_dec(x_43);
switch (x_44) {
case 2:
{
x_9 = x_31;
goto block_19;
}
case 4:
{
x_9 = x_31;
goto block_19;
}
case 5:
{
x_9 = x_31;
goto block_19;
}
case 1:
{
x_9 = x_31;
goto block_19;
}
default: 
{
x_20 = x_39;
goto block_23;
}
}
}
else
{
lean_dec(x_42);
x_20 = x_39;
goto block_23;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_45 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__2));
x_46 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__8, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__8);
x_47 = l_Lean_MessageData_ofConstName(x_1, x_32);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__10, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__10_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__10);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___redArg(x_45, x_50, x_4, x_5, x_6, x_7);
return x_51;
}
}
else
{
lean_dec_ref(x_33);
lean_dec(x_1);
goto block_28;
}
}
else
{
lean_dec_ref(x_30);
lean_dec(x_1);
goto block_28;
}
}
}
else
{
lean_object* x_63; lean_object* x_64; 
lean_dec(x_1);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
block_19:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__2));
x_11 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__4));
x_12 = l_Lean_Name_toString(x_1, x_9);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__6));
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = l_Lean_throwNamedError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable_spec__0___redArg(x_10, x_17, x_4, x_5, x_6, x_7);
return x_18;
}
block_23:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
else
{
x_9 = x_20;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_6 = l_Lean_BinderInfo_isImplicit(x_5);
if (x_6 == 0)
{
return x_1;
}
else
{
lean_object* x_7; uint8_t x_8; uint8_t x_19; 
lean_inc_ref(x_4);
x_7 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_4);
if (lean_obj_tag(x_7) == 5)
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_7, 1);
lean_inc_ref(x_30);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_dec_ref(x_31);
goto block_29;
}
else
{
uint8_t x_35; 
x_35 = lean_expr_has_loose_bvar(x_31, x_33);
if (x_35 == 0)
{
if (x_6 == 0)
{
lean_dec_ref(x_31);
goto block_18;
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec_ref(x_7);
lean_dec_ref(x_1);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_expr_lower_loose_bvars(x_31, x_36, x_36);
lean_dec_ref(x_31);
return x_37;
}
}
else
{
lean_dec_ref(x_31);
goto block_18;
}
}
}
else
{
lean_dec_ref(x_30);
goto block_29;
}
}
else
{
goto block_29;
}
block_12:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc_ref(x_3);
lean_inc(x_2);
lean_dec_ref(x_1);
x_9 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = l_Lean_instBEqBinderInfo_beq(x_5, x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc_ref(x_3);
lean_inc(x_2);
lean_dec_ref(x_1);
x_11 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_11;
}
else
{
lean_dec_ref(x_7);
return x_1;
}
}
}
block_18:
{
size_t x_13; uint8_t x_14; 
x_13 = lean_ptr_addr(x_3);
x_14 = lean_usize_dec_eq(x_13, x_13);
if (x_14 == 0)
{
x_8 = x_14;
goto block_12;
}
else
{
size_t x_15; size_t x_16; uint8_t x_17; 
x_15 = lean_ptr_addr(x_4);
x_16 = lean_ptr_addr(x_7);
x_17 = lean_usize_dec_eq(x_15, x_16);
x_8 = x_17;
goto block_12;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; 
lean_inc_ref(x_3);
lean_inc(x_2);
lean_dec_ref(x_1);
x_20 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = l_Lean_instBEqBinderInfo_beq(x_5, x_5);
if (x_21 == 0)
{
lean_object* x_22; 
lean_inc_ref(x_3);
lean_inc(x_2);
lean_dec_ref(x_1);
x_22 = l_Lean_Expr_lam___override(x_2, x_3, x_7, x_5);
return x_22;
}
else
{
lean_dec_ref(x_7);
return x_1;
}
}
}
block_29:
{
size_t x_24; uint8_t x_25; 
x_24 = lean_ptr_addr(x_3);
x_25 = lean_usize_dec_eq(x_24, x_24);
if (x_25 == 0)
{
x_19 = x_25;
goto block_23;
}
else
{
size_t x_26; size_t x_27; uint8_t x_28; 
x_26 = lean_ptr_addr(x_4);
x_27 = lean_ptr_addr(x_7);
x_28 = lean_usize_dec_eq(x_26, x_27);
x_19 = x_28;
goto block_23;
}
}
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_litToValue(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_9 = !lean_is_exclusive(x_1);
if (x_9 == 0)
{
x_3 = x_1;
x_4 = x_9;
goto block_8;
}
else
{
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = x_9;
goto block_8;
}
block_8:
{
lean_object* x_5; 
if (x_4 == 0)
{
x_5 = x_3;
goto block_6;
}
else
{
lean_object* x_7; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_2);
x_5 = x_7;
goto block_6;
}
block_6:
{
return x_5;
}
}
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; uint8_t x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
x_11 = x_1;
x_12 = x_17;
goto block_16;
}
else
{
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = x_17;
goto block_16;
}
block_16:
{
lean_object* x_13; 
if (x_12 == 0)
{
x_13 = x_11;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_10);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = l_Lean_Compiler_LCNF_ToLCNF_litToValue(x_1);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
x_11 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_9, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_dec_eq(x_2, x_7);
if (x_8 == 1)
{
lean_object* x_9; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
if (lean_obj_tag(x_1) == 6)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_12);
x_15 = lean_expr_instantiate1(x_13, x_14);
lean_dec_ref(x_14);
lean_dec_ref(x_13);
x_1 = x_15;
x_2 = x_11;
goto _start;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_nat_add(x_11, x_10);
lean_dec(x_11);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_17);
x_18 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_17, x_3, x_4, x_5);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_1 = x_19;
x_2 = x_17;
goto _start;
}
else
{
lean_dec(x_17);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_4, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__3);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg(x_1);
return x_3;
}
}
static lean_object* _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0(void) {
_start:
{
lean_object* x_1; 
x_1 = l_instMonadEST(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_75; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_75 = !lean_is_exclusive(x_10);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_10, 1);
lean_dec(x_76);
x_12 = x_10;
x_13 = x_75;
goto block_74;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_72; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_72 = !lean_is_exclusive(x_11);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_11, 1);
lean_dec(x_73);
x_18 = x_11;
x_19 = x_72;
goto block_71;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__1));
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_24);
lean_ctor_set(x_70, 1, x_20);
lean_ctor_set(x_70, 2, x_27);
lean_ctor_set(x_70, 3, x_26);
lean_ctor_set(x_70, 4, x_25);
x_28 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_28);
lean_ctor_set(x_68, 1, x_21);
x_29 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_65; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_65 = !lean_is_exclusive(x_30);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_30, 1);
lean_dec(x_66);
x_32 = x_30;
x_33 = x_65;
goto block_64;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_62; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_31, 1);
lean_dec(x_63);
x_38 = x_31;
x_39 = x_62;
goto block_61;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__3));
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_40);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set(x_60, 3, x_46);
lean_ctor_set(x_60, 4, x_45);
x_48 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_41);
x_49 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = lean_box(0);
x_52 = l_instInhabitedOfMonad___redArg(x_50, x_51);
x_53 = lean_alloc_closure((void*)(l_instInhabitedForall___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_53, 0, x_52);
x_54 = lean_panic_fn(x_53, x_1);
x_55 = lean_box(x_2);
x_56 = lean_apply_7(x_54, x_55, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_56;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_st_ref_get(x_4);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
x_12 = lean_box(1);
x_13 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_14 = 0;
x_15 = lean_unsigned_to_nat(0u);
x_16 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_17 = lean_box(0);
x_18 = 1;
x_19 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 1, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 2, x_14);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 3, x_18);
x_20 = lean_unsigned_to_nat(32u);
x_21 = lean_mk_empty_array_with_capacity(x_20);
lean_dec_ref(x_21);
x_22 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_23 = lean_st_mk_ref(x_22);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_23);
x_24 = lean_infer_type(x_1, x_19, x_23, x_7, x_8);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_st_ref_get(x_23);
lean_dec(x_23);
lean_dec(x_26);
x_27 = lean_box(x_3);
x_28 = lean_apply_8(x_2, x_25, x_27, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_28;
}
else
{
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_24, 0);
lean_inc(x_29);
lean_dec_ref(x_24);
x_30 = lean_box(x_3);
x_31 = lean_apply_8(x_2, x_29, x_30, x_4, x_5, x_6, x_7, x_8, lean_box(0));
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_32 = lean_ctor_get(x_24, 0);
x_39 = !lean_is_exclusive(x_24);
if (x_39 == 0)
{
x_33 = x_24;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_24);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_3, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
lean_dec(x_7);
lean_dec_ref(x_6);
x_12 = lean_ctor_get(x_9, 0);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_13 = x_9;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38_spec__41(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_75; 
x_9 = lean_obj_once(&l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0, &l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0_once, _init_l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__0);
x_10 = l_ReaderT_instMonad___redArg(x_9);
x_11 = lean_ctor_get(x_10, 0);
x_75 = !lean_is_exclusive(x_10);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_10, 1);
lean_dec(x_76);
x_12 = x_10;
x_13 = x_75;
goto block_74;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_72; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 2);
x_16 = lean_ctor_get(x_11, 3);
x_17 = lean_ctor_get(x_11, 4);
x_72 = !lean_is_exclusive(x_11);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = lean_ctor_get(x_11, 1);
lean_dec(x_73);
x_18 = x_11;
x_19 = x_72;
goto block_71;
}
else
{
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__1));
x_21 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__2));
lean_inc_ref(x_14);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_22, 0, x_14);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_23, 0, x_14);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_25, 0, x_17);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_16);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_27, 0, x_15);
if (x_19 == 0)
{
lean_ctor_set(x_18, 4, x_25);
lean_ctor_set(x_18, 3, x_26);
lean_ctor_set(x_18, 2, x_27);
lean_ctor_set(x_18, 1, x_20);
lean_ctor_set(x_18, 0, x_24);
x_28 = x_18;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_24);
lean_ctor_set(x_70, 1, x_20);
lean_ctor_set(x_70, 2, x_27);
lean_ctor_set(x_70, 3, x_26);
lean_ctor_set(x_70, 4, x_25);
x_28 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_29; 
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_21);
lean_ctor_set(x_12, 0, x_28);
x_29 = x_12;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_28);
lean_ctor_set(x_68, 1, x_21);
x_29 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_65; 
x_30 = l_ReaderT_instMonad___redArg(x_29);
x_31 = lean_ctor_get(x_30, 0);
x_65 = !lean_is_exclusive(x_30);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = lean_ctor_get(x_30, 1);
lean_dec(x_66);
x_32 = x_30;
x_33 = x_65;
goto block_64;
}
else
{
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_box(0);
x_33 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_62; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 2);
x_36 = lean_ctor_get(x_31, 3);
x_37 = lean_ctor_get(x_31, 4);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_31, 1);
lean_dec(x_63);
x_38 = x_31;
x_39 = x_62;
goto block_61;
}
else
{
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_38 = lean_box(0);
x_39 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__3));
x_41 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2___closed__4));
lean_inc_ref(x_34);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_42, 0, x_34);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_43, 0, x_34);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_37);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_46, 0, x_36);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__4), 6, 1);
lean_closure_set(x_47, 0, x_35);
if (x_39 == 0)
{
lean_ctor_set(x_38, 4, x_45);
lean_ctor_set(x_38, 3, x_46);
lean_ctor_set(x_38, 2, x_47);
lean_ctor_set(x_38, 1, x_40);
lean_ctor_set(x_38, 0, x_44);
x_48 = x_38;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_60, 0, x_44);
lean_ctor_set(x_60, 1, x_40);
lean_ctor_set(x_60, 2, x_47);
lean_ctor_set(x_60, 3, x_46);
lean_ctor_set(x_60, 4, x_45);
x_48 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_49; 
if (x_33 == 0)
{
lean_ctor_set(x_32, 1, x_41);
lean_ctor_set(x_32, 0, x_48);
x_49 = x_32;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_41);
x_49 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_50 = l_ReaderT_instMonad___redArg(x_49);
x_51 = l_ReaderT_instMonad___redArg(x_50);
x_52 = lean_box(0);
x_53 = l_instInhabitedOfMonad___redArg(x_51, x_52);
x_54 = lean_panic_fn(x_53, x_1);
x_55 = lean_box(x_2);
x_56 = lean_apply_7(x_54, x_55, x_3, x_4, x_5, x_6, x_7, lean_box(0));
return x_56;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38_spec__41___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_panic___at___00Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38_spec__41(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
static lean_object* _init_l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(11u);
x_3 = lean_unsigned_to_nat(122u);
x_4 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__1));
x_5 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_9 = lean_st_ref_get(x_7);
x_13 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_13);
lean_dec(x_9);
x_14 = 0;
x_15 = l_Lean_Environment_findAsync_x3f(x_13, x_1, x_14);
if (lean_obj_tag(x_15) == 1)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_35; 
x_16 = lean_ctor_get(x_15, 0);
x_35 = !lean_is_exclusive(x_15);
if (x_35 == 0)
{
x_17 = x_15;
x_18 = x_35;
goto block_34;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_35;
goto block_34;
}
block_34:
{
uint8_t x_19; 
x_19 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
if (x_19 == 6)
{
lean_object* x_20; 
x_20 = l_Lean_AsyncConstantInfo_toConstantInfo(x_16);
if (lean_obj_tag(x_20) == 6)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_31; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_20, 0);
x_31 = !lean_is_exclusive(x_20);
if (x_31 == 0)
{
x_22 = x_20;
x_23 = x_31;
goto block_30;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_24; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_21);
x_24 = x_17;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_21);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_23 == 0)
{
lean_ctor_set_tag(x_22, 0);
lean_ctor_set(x_22, 0, x_24);
x_25 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_20);
lean_del_object(x_17);
x_32 = lean_obj_once(&l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__3, &l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__3_once, _init_l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__3);
x_33 = l_panic___at___00Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38_spec__41(x_32, x_2, x_3, x_4, x_5, x_6, x_7);
return x_33;
}
}
else
{
lean_del_object(x_17);
lean_dec(x_16);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
goto block_12;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
goto block_12;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_forallBoundedTelescope___at___00Lean_Compiler_LCNF_ToLCNF_etaExpandN_spec__0___redArg___lam__0___boxed), 8, 1);
lean_closure_set(x_9, 0, x_2);
x_10 = 0;
x_11 = lean_box(0);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), x_10, x_11, x_1, x_9, x_3, x_10, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
x_14 = x_12;
x_15 = x_20;
goto block_19;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_16; 
if (x_15 == 0)
{
x_16 = x_14;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_13);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
x_21 = lean_ctor_get(x_12, 0);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
x_22 = x_12;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_12);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_49; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get(x_2, 2);
x_49 = !lean_is_exclusive(x_2);
if (x_49 == 0)
{
x_12 = x_2;
x_13 = x_49;
goto block_48;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_12 = lean_box(0);
x_13 = x_49;
goto block_48;
}
block_48:
{
uint8_t x_14; 
x_14 = lean_nat_dec_lt(x_10, x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_3);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget_borrowed(x_9, x_10);
x_17 = l_Lean_Expr_fvarId_x21(x_16);
lean_inc_ref(x_4);
x_18 = l_Lean_FVarId_getType___redArg(x_17, x_4, x_6, x_7);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_20 = l_Lean_Meta_isProp(x_19, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec_ref(x_20);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_10, x_22);
lean_dec(x_10);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_23);
x_24 = x_12;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_11);
x_24 = x_31;
goto block_30;
}
block_30:
{
uint8_t x_25; 
x_25 = lean_unbox(x_21);
lean_dec(x_21);
if (x_25 == 0)
{
if (x_1 == 0)
{
x_2 = x_24;
goto _start;
}
else
{
lean_object* x_27; 
x_27 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
x_2 = x_24;
x_3 = x_27;
goto _start;
}
}
else
{
x_2 = x_24;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_32 = lean_ctor_get(x_20, 0);
x_39 = !lean_is_exclusive(x_20);
if (x_39 == 0)
{
x_33 = x_20;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_20);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_40 = lean_ctor_get(x_18, 0);
x_47 = !lean_is_exclusive(x_18);
if (x_47 == 0)
{
x_41 = x_18;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_18);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
x_10 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___redArg(x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; uint8_t x_17; 
x_10 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_3);
x_17 = lean_nat_dec_le(x_2, x_10);
if (x_17 == 0)
{
x_11 = x_2;
x_12 = x_16;
goto block_15;
}
else
{
lean_dec(x_2);
x_11 = x_10;
x_12 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Array_toSubarray___redArg(x_3, x_11, x_12);
x_14 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___redArg(x_1, x_13, x_10, x_5, x_6, x_7, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_4, 2);
x_8 = lean_ctor_get(x_4, 5);
x_9 = lean_st_ref_get(x_5);
x_10 = lean_st_ref_get(x_3);
x_11 = l_Lean_Compiler_LCNF_getPurity___redArg(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_34; 
x_12 = lean_ctor_get(x_11, 0);
x_34 = !lean_is_exclusive(x_11);
if (x_34 == 0)
{
x_13 = x_11;
x_14 = x_34;
goto block_33;
}
else
{
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_31; 
x_15 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_15);
lean_dec(x_9);
x_16 = lean_ctor_get(x_10, 0);
x_31 = !lean_is_exclusive(x_10);
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_10, 1);
lean_dec(x_32);
x_17 = x_10;
x_18 = x_31;
goto block_30;
}
else
{
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(0);
x_18 = x_31;
goto block_30;
}
block_30:
{
uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_unbox(x_12);
lean_dec(x_12);
x_20 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_16, x_19);
lean_dec_ref(x_16);
x_21 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2);
lean_inc_ref(x_7);
x_22 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_20);
lean_ctor_set(x_22, 3, x_7);
if (x_18 == 0)
{
lean_ctor_set_tag(x_17, 3);
lean_ctor_set(x_17, 1, x_1);
lean_ctor_set(x_17, 0, x_22);
x_23 = x_17;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_1);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_23);
if (x_14 == 0)
{
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 0, x_24);
x_25 = x_13;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec_ref(x_1);
x_35 = lean_ctor_get(x_11, 0);
x_42 = !lean_is_exclusive(x_11);
if (x_42 == 0)
{
x_36 = x_11;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_39; lean_object* x_40; lean_object* x_103; lean_object* x_104; lean_object* x_130; lean_object* x_131; lean_object* x_157; lean_object* x_158; lean_object* x_184; lean_object* x_185; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; uint8_t x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_211 = lean_ctor_get(x_1, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_1, 2);
lean_inc(x_212);
lean_dec_ref(x_1);
x_240 = lean_st_ref_get(x_8);
x_241 = lean_ctor_get(x_240, 0);
lean_inc_ref(x_241);
lean_dec(x_240);
x_242 = lean_box(1);
x_243 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_244 = 0;
x_245 = lean_unsigned_to_nat(0u);
x_246 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_247 = lean_box(0);
x_248 = 1;
x_249 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_249, 0, x_243);
lean_ctor_set(x_249, 1, x_242);
lean_ctor_set(x_249, 2, x_241);
lean_ctor_set(x_249, 3, x_246);
lean_ctor_set(x_249, 4, x_247);
lean_ctor_set(x_249, 5, x_245);
lean_ctor_set(x_249, 6, x_247);
lean_ctor_set_uint8(x_249, sizeof(void*)*7, x_244);
lean_ctor_set_uint8(x_249, sizeof(void*)*7 + 1, x_244);
lean_ctor_set_uint8(x_249, sizeof(void*)*7 + 2, x_244);
lean_ctor_set_uint8(x_249, sizeof(void*)*7 + 3, x_248);
x_250 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_251 = lean_st_mk_ref(x_250);
lean_inc_ref(x_5);
x_252 = lean_array_get_borrowed(x_5, x_6, x_211);
lean_dec(x_211);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_251);
lean_inc(x_252);
x_253 = lean_whnf(x_252, x_249, x_251, x_11, x_12);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
lean_dec_ref(x_253);
x_255 = lean_st_ref_get(x_251);
lean_dec(x_251);
lean_dec(x_255);
x_213 = x_254;
goto block_239;
}
else
{
lean_dec(x_251);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_256; 
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
lean_dec_ref(x_253);
x_213 = x_256;
goto block_239;
}
else
{
lean_object* x_257; lean_object* x_258; uint8_t x_259; uint8_t x_264; 
lean_dec(x_212);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_257 = lean_ctor_get(x_253, 0);
x_264 = !lean_is_exclusive(x_253);
if (x_264 == 0)
{
x_258 = x_253;
x_259 = x_264;
goto block_263;
}
else
{
lean_inc(x_257);
lean_dec(x_253);
x_258 = lean_box(0);
x_259 = x_264;
goto block_263;
}
block_263:
{
lean_object* x_260; 
if (x_259 == 0)
{
x_260 = x_258;
goto block_261;
}
else
{
lean_object* x_262; 
x_262 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_262, 0, x_257);
x_260 = x_262;
goto block_261;
}
block_261:
{
return x_260;
}
}
}
}
block_239:
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_214 = lean_st_ref_get(x_8);
x_215 = lean_ctor_get(x_214, 0);
lean_inc_ref(x_215);
lean_dec(x_214);
x_216 = lean_box(1);
x_217 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_218 = 0;
x_219 = lean_unsigned_to_nat(0u);
x_220 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_221 = lean_box(0);
x_222 = 1;
x_223 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_223, 0, x_217);
lean_ctor_set(x_223, 1, x_216);
lean_ctor_set(x_223, 2, x_215);
lean_ctor_set(x_223, 3, x_220);
lean_ctor_set(x_223, 4, x_221);
lean_ctor_set(x_223, 5, x_219);
lean_ctor_set(x_223, 6, x_221);
lean_ctor_set_uint8(x_223, sizeof(void*)*7, x_218);
lean_ctor_set_uint8(x_223, sizeof(void*)*7 + 1, x_218);
lean_ctor_set_uint8(x_223, sizeof(void*)*7 + 2, x_218);
lean_ctor_set_uint8(x_223, sizeof(void*)*7 + 3, x_222);
x_224 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_225 = lean_st_mk_ref(x_224);
x_226 = lean_array_get_borrowed(x_5, x_6, x_212);
lean_dec(x_212);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_225);
lean_inc(x_226);
x_227 = lean_whnf(x_226, x_223, x_225, x_11, x_12);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; lean_object* x_229; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
lean_dec_ref(x_227);
x_229 = lean_st_ref_get(x_225);
lean_dec(x_225);
lean_dec(x_229);
x_184 = x_213;
x_185 = x_228;
goto block_210;
}
else
{
lean_dec(x_225);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_230; 
x_230 = lean_ctor_get(x_227, 0);
lean_inc(x_230);
lean_dec_ref(x_227);
x_184 = x_213;
x_185 = x_230;
goto block_210;
}
else
{
lean_object* x_231; lean_object* x_232; uint8_t x_233; uint8_t x_238; 
lean_dec_ref(x_213);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_231 = lean_ctor_get(x_227, 0);
x_238 = !lean_is_exclusive(x_227);
if (x_238 == 0)
{
x_232 = x_227;
x_233 = x_238;
goto block_237;
}
else
{
lean_inc(x_231);
lean_dec(x_227);
x_232 = lean_box(0);
x_233 = x_238;
goto block_237;
}
block_237:
{
lean_object* x_234; 
if (x_233 == 0)
{
x_234 = x_232;
goto block_235;
}
else
{
lean_object* x_236; 
x_236 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_236, 0, x_231);
x_234 = x_236;
goto block_235;
}
block_235:
{
return x_234;
}
}
}
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
lean_dec_ref(x_5);
lean_dec_ref(x_3);
lean_dec(x_2);
x_265 = lean_ctor_get(x_1, 1);
lean_inc(x_265);
lean_dec_ref(x_1);
x_266 = lean_box(x_7);
x_267 = lean_apply_8(x_4, x_265, x_266, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_267;
}
block_26:
{
lean_object* x_15; 
lean_inc(x_12);
lean_inc_ref(x_11);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_14, x_8, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg(x_16, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_25; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_18 = lean_ctor_get(x_15, 0);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
x_19 = x_15;
x_20 = x_25;
goto block_24;
}
else
{
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(0);
x_20 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_21; 
if (x_20 == 0)
{
x_21 = x_19;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
block_38:
{
lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__1, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__1);
x_32 = 0;
x_33 = l_Lean_MessageData_ofConstName(x_2, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___redArg(x_36, x_27, x_28, x_29, x_30);
lean_dec(x_30);
lean_dec_ref(x_29);
lean_dec(x_28);
lean_dec_ref(x_27);
return x_37;
}
block_102:
{
if (lean_obj_tag(x_39) == 1)
{
if (lean_obj_tag(x_40) == 1)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_2);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec_ref(x_39);
x_42 = lean_ctor_get(x_41, 0);
lean_inc_ref(x_42);
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
lean_dec_ref(x_40);
x_44 = lean_ctor_get(x_43, 0);
lean_inc_ref(x_44);
lean_dec(x_43);
x_45 = lean_ctor_get(x_41, 3);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 2);
lean_inc_ref(x_47);
lean_dec_ref(x_42);
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec_ref(x_44);
x_49 = lean_name_eq(x_46, x_48);
lean_dec(x_48);
lean_dec(x_46);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_47);
lean_dec(x_45);
lean_dec_ref(x_4);
x_50 = lean_st_ref_get(x_8);
x_51 = lean_ctor_get(x_50, 0);
lean_inc_ref(x_51);
lean_dec(x_50);
x_52 = lean_box(1);
x_53 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_54 = lean_unsigned_to_nat(0u);
x_55 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_56 = lean_box(0);
x_57 = 1;
x_58 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_52);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_58, 4, x_56);
lean_ctor_set(x_58, 5, x_54);
lean_ctor_set(x_58, 6, x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*7, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 1, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 2, x_49);
lean_ctor_set_uint8(x_58, sizeof(void*)*7 + 3, x_57);
x_59 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_60 = lean_st_mk_ref(x_59);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_60);
x_61 = lean_infer_type(x_3, x_58, x_60, x_11, x_12);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_63 = lean_st_ref_get(x_60);
lean_dec(x_60);
lean_dec(x_63);
x_14 = x_62;
goto block_26;
}
else
{
lean_dec(x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_64; 
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
lean_dec_ref(x_61);
x_14 = x_64;
goto block_26;
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; uint8_t x_72; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
x_65 = lean_ctor_get(x_61, 0);
x_72 = !lean_is_exclusive(x_61);
if (x_72 == 0)
{
x_66 = x_61;
x_67 = x_72;
goto block_71;
}
else
{
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_box(0);
x_67 = x_72;
goto block_71;
}
block_71:
{
lean_object* x_68; 
if (x_67 == 0)
{
x_68 = x_66;
goto block_69;
}
else
{
lean_object* x_70; 
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_68 = x_70;
goto block_69;
}
block_69:
{
return x_68;
}
}
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec_ref(x_3);
x_73 = lean_st_ref_get(x_8);
x_74 = lean_ctor_get(x_73, 0);
lean_inc_ref(x_74);
lean_dec(x_73);
x_75 = lean_box(1);
x_76 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_77 = 0;
x_78 = lean_unsigned_to_nat(0u);
x_79 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_81, 0, x_76);
lean_ctor_set(x_81, 1, x_75);
lean_ctor_set(x_81, 2, x_74);
lean_ctor_set(x_81, 3, x_79);
lean_ctor_set(x_81, 4, x_80);
lean_ctor_set(x_81, 5, x_78);
lean_ctor_set(x_81, 6, x_80);
lean_ctor_set_uint8(x_81, sizeof(void*)*7, x_77);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 1, x_77);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 2, x_77);
lean_ctor_set_uint8(x_81, sizeof(void*)*7 + 3, x_49);
x_82 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_83 = lean_st_mk_ref(x_82);
x_84 = lean_box(x_49);
x_85 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__2___boxed), 9, 2);
lean_closure_set(x_85, 0, x_84);
lean_closure_set(x_85, 1, x_45);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_83);
x_86 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___redArg(x_47, x_85, x_77, x_81, x_83, x_11, x_12);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_st_ref_get(x_83);
lean_dec(x_83);
lean_dec(x_88);
x_89 = lean_box(x_7);
x_90 = lean_apply_8(x_4, x_87, x_89, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_90;
}
else
{
lean_dec(x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_86, 0);
lean_inc(x_91);
lean_dec_ref(x_86);
x_92 = lean_box(x_7);
x_93 = lean_apply_8(x_4, x_91, x_92, x_8, x_9, x_10, x_11, x_12, lean_box(0));
return x_93;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
x_94 = lean_ctor_get(x_86, 0);
x_101 = !lean_is_exclusive(x_86);
if (x_101 == 0)
{
x_95 = x_86;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_86);
x_95 = lean_box(0);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_96 == 0)
{
x_97 = x_95;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
}
}
else
{
lean_dec_ref(x_39);
lean_dec(x_40);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = x_12;
goto block_38;
}
}
else
{
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_27 = x_9;
x_28 = x_10;
x_29 = x_11;
x_30 = x_12;
goto block_38;
}
}
block_129:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_105 = lean_st_ref_get(x_8);
x_106 = lean_ctor_get(x_105, 0);
lean_inc_ref(x_106);
lean_dec(x_105);
x_107 = lean_box(1);
x_108 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_109 = 0;
x_110 = lean_unsigned_to_nat(0u);
x_111 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_112 = lean_box(0);
x_113 = 1;
x_114 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_107);
lean_ctor_set(x_114, 2, x_106);
lean_ctor_set(x_114, 3, x_111);
lean_ctor_set(x_114, 4, x_112);
lean_ctor_set(x_114, 5, x_110);
lean_ctor_set(x_114, 6, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*7, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 1, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 2, x_109);
lean_ctor_set_uint8(x_114, sizeof(void*)*7 + 3, x_113);
x_115 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_116 = lean_st_mk_ref(x_115);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_116);
x_117 = l_Lean_Meta_isConstructorApp_x3f(x_103, x_114, x_116, x_11, x_12);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
lean_dec_ref(x_117);
x_119 = lean_st_ref_get(x_116);
lean_dec(x_116);
lean_dec(x_119);
x_39 = x_104;
x_40 = x_118;
goto block_102;
}
else
{
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
lean_dec_ref(x_117);
x_39 = x_104;
x_40 = x_120;
goto block_102;
}
else
{
lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_128; 
lean_dec(x_104);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_121 = lean_ctor_get(x_117, 0);
x_128 = !lean_is_exclusive(x_117);
if (x_128 == 0)
{
x_122 = x_117;
x_123 = x_128;
goto block_127;
}
else
{
lean_inc(x_121);
lean_dec(x_117);
x_122 = lean_box(0);
x_123 = x_128;
goto block_127;
}
block_127:
{
lean_object* x_124; 
if (x_123 == 0)
{
x_124 = x_122;
goto block_125;
}
else
{
lean_object* x_126; 
x_126 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_126, 0, x_121);
x_124 = x_126;
goto block_125;
}
block_125:
{
return x_124;
}
}
}
}
}
block_156:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_132 = lean_st_ref_get(x_8);
x_133 = lean_ctor_get(x_132, 0);
lean_inc_ref(x_133);
lean_dec(x_132);
x_134 = lean_box(1);
x_135 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_136 = 0;
x_137 = lean_unsigned_to_nat(0u);
x_138 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_139 = lean_box(0);
x_140 = 1;
x_141 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_134);
lean_ctor_set(x_141, 2, x_133);
lean_ctor_set(x_141, 3, x_138);
lean_ctor_set(x_141, 4, x_139);
lean_ctor_set(x_141, 5, x_137);
lean_ctor_set(x_141, 6, x_139);
lean_ctor_set_uint8(x_141, sizeof(void*)*7, x_136);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 1, x_136);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 2, x_136);
lean_ctor_set_uint8(x_141, sizeof(void*)*7 + 3, x_140);
x_142 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_143 = lean_st_mk_ref(x_142);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_143);
x_144 = l_Lean_Meta_isConstructorApp_x3f(x_130, x_141, x_143, x_11, x_12);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
lean_dec_ref(x_144);
x_146 = lean_st_ref_get(x_143);
lean_dec(x_143);
lean_dec(x_146);
x_103 = x_131;
x_104 = x_145;
goto block_129;
}
else
{
lean_dec(x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_147; 
x_147 = lean_ctor_get(x_144, 0);
lean_inc(x_147);
lean_dec_ref(x_144);
x_103 = x_131;
x_104 = x_147;
goto block_129;
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; uint8_t x_155; 
lean_dec_ref(x_131);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_148 = lean_ctor_get(x_144, 0);
x_155 = !lean_is_exclusive(x_144);
if (x_155 == 0)
{
x_149 = x_144;
x_150 = x_155;
goto block_154;
}
else
{
lean_inc(x_148);
lean_dec(x_144);
x_149 = lean_box(0);
x_150 = x_155;
goto block_154;
}
block_154:
{
lean_object* x_151; 
if (x_150 == 0)
{
x_151 = x_149;
goto block_152;
}
else
{
lean_object* x_153; 
x_153 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_153, 0, x_148);
x_151 = x_153;
goto block_152;
}
block_152:
{
return x_151;
}
}
}
}
}
block_183:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_159 = lean_st_ref_get(x_8);
x_160 = lean_ctor_get(x_159, 0);
lean_inc_ref(x_160);
lean_dec(x_159);
x_161 = lean_box(1);
x_162 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_163 = 0;
x_164 = lean_unsigned_to_nat(0u);
x_165 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_166 = lean_box(0);
x_167 = 1;
x_168 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_168, 0, x_162);
lean_ctor_set(x_168, 1, x_161);
lean_ctor_set(x_168, 2, x_160);
lean_ctor_set(x_168, 3, x_165);
lean_ctor_set(x_168, 4, x_166);
lean_ctor_set(x_168, 5, x_164);
lean_ctor_set(x_168, 6, x_166);
lean_ctor_set_uint8(x_168, sizeof(void*)*7, x_163);
lean_ctor_set_uint8(x_168, sizeof(void*)*7 + 1, x_163);
lean_ctor_set_uint8(x_168, sizeof(void*)*7 + 2, x_163);
lean_ctor_set_uint8(x_168, sizeof(void*)*7 + 3, x_167);
x_169 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_170 = lean_st_mk_ref(x_169);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_170);
x_171 = l_Lean_Expr_toCtorIfLit(x_157, x_168, x_170, x_11, x_12);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec_ref(x_171);
x_173 = lean_st_ref_get(x_170);
lean_dec(x_170);
lean_dec(x_173);
x_130 = x_158;
x_131 = x_172;
goto block_156;
}
else
{
lean_dec(x_170);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_171, 0);
lean_inc(x_174);
lean_dec_ref(x_171);
x_130 = x_158;
x_131 = x_174;
goto block_156;
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; uint8_t x_182; 
lean_dec_ref(x_158);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_175 = lean_ctor_get(x_171, 0);
x_182 = !lean_is_exclusive(x_171);
if (x_182 == 0)
{
x_176 = x_171;
x_177 = x_182;
goto block_181;
}
else
{
lean_inc(x_175);
lean_dec(x_171);
x_176 = lean_box(0);
x_177 = x_182;
goto block_181;
}
block_181:
{
lean_object* x_178; 
if (x_177 == 0)
{
x_178 = x_176;
goto block_179;
}
else
{
lean_object* x_180; 
x_180 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_180, 0, x_175);
x_178 = x_180;
goto block_179;
}
block_179:
{
return x_178;
}
}
}
}
}
block_210:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_186 = lean_st_ref_get(x_8);
x_187 = lean_ctor_get(x_186, 0);
lean_inc_ref(x_187);
lean_dec(x_186);
x_188 = lean_box(1);
x_189 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_190 = 0;
x_191 = lean_unsigned_to_nat(0u);
x_192 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_193 = lean_box(0);
x_194 = 1;
x_195 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_188);
lean_ctor_set(x_195, 2, x_187);
lean_ctor_set(x_195, 3, x_192);
lean_ctor_set(x_195, 4, x_193);
lean_ctor_set(x_195, 5, x_191);
lean_ctor_set(x_195, 6, x_193);
lean_ctor_set_uint8(x_195, sizeof(void*)*7, x_190);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 1, x_190);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 2, x_190);
lean_ctor_set_uint8(x_195, sizeof(void*)*7 + 3, x_194);
x_196 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_197 = lean_st_mk_ref(x_196);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_197);
x_198 = l_Lean_Expr_toCtorIfLit(x_184, x_195, x_197, x_11, x_12);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
lean_dec_ref(x_198);
x_200 = lean_st_ref_get(x_197);
lean_dec(x_197);
lean_dec(x_200);
x_157 = x_185;
x_158 = x_199;
goto block_183;
}
else
{
lean_dec(x_197);
if (lean_obj_tag(x_198) == 0)
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_198, 0);
lean_inc(x_201);
lean_dec_ref(x_198);
x_157 = x_185;
x_158 = x_201;
goto block_183;
}
else
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; uint8_t x_209; 
lean_dec_ref(x_185);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
x_202 = lean_ctor_get(x_198, 0);
x_209 = !lean_is_exclusive(x_198);
if (x_209 == 0)
{
x_203 = x_198;
x_204 = x_209;
goto block_208;
}
else
{
lean_inc(x_202);
lean_dec(x_198);
x_203 = lean_box(0);
x_204 = x_209;
goto block_208;
}
block_208:
{
lean_object* x_205; 
if (x_204 == 0)
{
x_205 = x_203;
goto block_206;
}
else
{
lean_object* x_207; 
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_202);
x_205 = x_207;
goto block_206;
}
block_206:
{
return x_205;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
x_15 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_6);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_34; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 2);
x_13 = lean_ctor_get(x_7, 3);
x_14 = lean_ctor_get(x_7, 4);
x_15 = lean_ctor_get(x_7, 5);
x_16 = lean_ctor_get(x_7, 6);
x_17 = lean_ctor_get(x_7, 7);
x_18 = lean_ctor_get(x_7, 8);
x_19 = lean_ctor_get(x_7, 9);
x_20 = lean_ctor_get(x_7, 10);
x_21 = lean_ctor_get(x_7, 11);
x_22 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_23 = lean_ctor_get(x_7, 12);
x_24 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_25 = lean_ctor_get(x_7, 13);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
x_26 = x_7;
x_27 = x_34;
goto block_33;
}
else
{
lean_inc(x_25);
lean_inc(x_23);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_7);
x_26 = lean_box(0);
x_27 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_28; lean_object* x_29; 
x_28 = l_Lean_replaceRef(x_1, x_15);
lean_dec(x_15);
if (x_27 == 0)
{
lean_ctor_set(x_26, 5, x_28);
x_29 = x_26;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_32, 0, x_10);
lean_ctor_set(x_32, 1, x_11);
lean_ctor_set(x_32, 2, x_12);
lean_ctor_set(x_32, 3, x_13);
lean_ctor_set(x_32, 4, x_14);
lean_ctor_set(x_32, 5, x_28);
lean_ctor_set(x_32, 6, x_16);
lean_ctor_set(x_32, 7, x_17);
lean_ctor_set(x_32, 8, x_18);
lean_ctor_set(x_32, 9, x_19);
lean_ctor_set(x_32, 10, x_20);
lean_ctor_set(x_32, 11, x_21);
lean_ctor_set(x_32, 12, x_23);
lean_ctor_set(x_32, 13, x_25);
lean_ctor_set_uint8(x_32, sizeof(void*)*14, x_22);
lean_ctor_set_uint8(x_32, sizeof(void*)*14 + 1, x_24);
x_29 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_30; 
x_30 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___redArg(x_2, x_5, x_6, x_29, x_8);
lean_dec_ref(x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_box(1);
x_2 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3);
x_3 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__3));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__5));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__7));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__14(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__13));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_st_ref_get(x_3);
x_6 = lean_ctor_get(x_5, 0);
lean_inc_ref(x_6);
lean_dec(x_5);
x_7 = l_Lean_Name_isAnonymous(x_2);
if (x_7 == 0)
{
uint8_t x_8; 
x_8 = lean_ctor_get_uint8(x_6, sizeof(void*)*8);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
lean_inc_ref(x_6);
x_10 = l_Lean_Environment_setExporting(x_6, x_7);
lean_inc(x_2);
lean_inc_ref(x_10);
x_11 = l_Lean_Environment_contains(x_10, x_2, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_10);
lean_dec_ref(x_6);
lean_dec(x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__2);
x_14 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__0);
x_15 = l_Lean_Options_empty;
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_14);
lean_ctor_set(x_16, 3, x_15);
lean_inc(x_2);
x_17 = l_Lean_MessageData_ofConstName(x_2, x_7);
x_18 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_Environment_getModuleIdxFor_x3f(x_6, x_2);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_20 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__4);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_MessageData_note(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_62; 
x_27 = lean_ctor_get(x_19, 0);
x_62 = !lean_is_exclusive(x_19);
if (x_62 == 0)
{
x_28 = x_19;
x_29 = x_62;
goto block_61;
}
else
{
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_box(0);
x_29 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_box(0);
x_31 = l_Lean_Environment_header(x_6);
lean_dec_ref(x_6);
x_32 = l_Lean_EnvironmentHeader_moduleNames(x_31);
x_33 = lean_array_get(x_30, x_32, x_27);
lean_dec(x_27);
lean_dec_ref(x_32);
x_34 = l_Lean_isPrivateName(x_2);
lean_dec(x_2);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_35 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__6);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_18);
x_37 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__8);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_MessageData_ofName(x_33);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__10);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_MessageData_note(x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_44);
x_45 = x_28;
goto block_46;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_45 = x_47;
goto block_46;
}
block_46:
{
return x_45;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_48 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__2);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_18);
x_50 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__12);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_MessageData_ofName(x_33);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___closed__14);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_MessageData_note(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
if (x_29 == 0)
{
lean_ctor_set_tag(x_28, 0);
lean_ctor_set(x_28, 0, x_57);
x_58 = x_28;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_57);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
}
}
}
else
{
lean_object* x_63; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_1);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_10 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg(x_1, x_2, x_8);
x_11 = lean_ctor_get(x_10, 0);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
x_12 = x_10;
x_13 = x_20;
goto block_19;
}
else
{
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = x_20;
goto block_19;
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l_Lean_unknownIdentifierMessageTag;
x_15 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
if (x_13 == 0)
{
lean_ctor_set(x_12, 0, x_15);
x_16 = x_12;
goto block_17;
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_15);
x_16 = x_18;
goto block_17;
}
block_17:
{
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___redArg(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___redArg(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___closed__1);
x_11 = 0;
lean_inc(x_2);
x_12 = l_Lean_MessageData_ofConstName(x_2, x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___closed__2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___redArg(x_1, x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_6, 5);
lean_inc(x_9);
x_10 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg(x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = 0;
lean_inc(x_1);
x_12 = l_Lean_Environment_find_x3f(x_10, x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_21; 
lean_dec_ref(x_6);
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
x_21 = !lean_is_exclusive(x_12);
if (x_21 == 0)
{
x_15 = x_12;
x_16 = x_21;
goto block_20;
}
else
{
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = x_21;
goto block_20;
}
block_20:
{
lean_object* x_17; 
if (x_16 == 0)
{
lean_ctor_set_tag(x_15, 0);
x_17 = x_15;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_st_ref_get(x_5);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_box(1);
x_14 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_15 = 0;
x_16 = lean_mk_empty_array_with_capacity(x_1);
x_17 = lean_box(0);
x_18 = 1;
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_16);
lean_ctor_set(x_19, 4, x_17);
lean_ctor_set(x_19, 5, x_1);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*7, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 1, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 2, x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 3, x_18);
x_20 = lean_obj_once(&l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1, &l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1_once, _init_l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go_spec__5___redArg___closed__1);
lean_inc_n(x_1, 3);
x_21 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_1);
lean_ctor_set(x_21, 2, x_1);
lean_ctor_set(x_21, 3, x_20);
lean_ctor_set(x_21, 4, x_20);
lean_ctor_set(x_21, 5, x_20);
lean_ctor_set(x_21, 6, x_20);
lean_ctor_set(x_21, 7, x_20);
lean_ctor_set(x_21, 8, x_20);
x_22 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__1);
x_23 = lean_unsigned_to_nat(32u);
x_24 = lean_mk_empty_array_with_capacity(x_23);
x_25 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__2);
x_26 = 5;
lean_inc(x_1);
x_27 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_1);
lean_ctor_set(x_27, 3, x_1);
lean_ctor_set_usize(x_27, 4, x_26);
x_28 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__4);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_13);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_st_mk_ref(x_29);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_30);
x_31 = lean_infer_type(x_2, x_19, x_30, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = lean_st_ref_get(x_30);
lean_dec(x_30);
lean_dec(x_33);
x_34 = lean_box(x_4);
x_35 = lean_apply_8(x_3, x_32, x_34, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_35;
}
else
{
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_31, 0);
lean_inc(x_36);
lean_dec_ref(x_31);
x_37 = lean_box(x_4);
x_38 = lean_apply_8(x_3, x_36, x_37, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_46; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_39 = lean_ctor_get(x_31, 0);
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
x_40 = x_31;
x_41 = x_46;
goto block_45;
}
else
{
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_box(0);
x_41 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_42; 
if (x_41 == 0)
{
x_42 = x_40;
goto block_43;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_39);
x_42 = x_44;
goto block_43;
}
block_43:
{
return x_42;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__2(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_2, x_1);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_array_uget(x_3, x_2);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_Param_toExpr___redArg(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_14 = l_Lean_Compiler_LCNF_inferType(x_13, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc(x_8);
lean_inc_ref(x_7);
x_16 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_15, x_4, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; uint8_t x_49; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_uset(x_3, x_2, x_18);
x_20 = 0;
x_49 = lean_unbox(x_17);
lean_dec(x_17);
if (x_49 == 0)
{
lean_inc(x_6);
x_21 = x_4;
x_22 = x_6;
goto block_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_67; 
x_50 = lean_st_ref_take(x_4);
x_51 = lean_ctor_get(x_50, 0);
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get_uint8(x_50, sizeof(void*)*6);
x_54 = lean_ctor_get(x_50, 2);
x_55 = lean_ctor_get(x_50, 3);
x_56 = lean_ctor_get(x_50, 4);
x_57 = lean_ctor_get(x_50, 5);
x_67 = !lean_is_exclusive(x_50);
if (x_67 == 0)
{
x_58 = x_50;
x_59 = x_67;
goto block_66;
}
else
{
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_50);
x_58 = lean_box(0);
x_59 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_12, 0);
lean_inc(x_60);
x_61 = l_Lean_FVarIdSet_insert(x_57, x_60);
if (x_59 == 0)
{
lean_ctor_set(x_58, 5, x_61);
x_62 = x_58;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_65, 0, x_51);
lean_ctor_set(x_65, 1, x_52);
lean_ctor_set(x_65, 2, x_54);
lean_ctor_set(x_65, 3, x_55);
lean_ctor_set(x_65, 4, x_56);
lean_ctor_set(x_65, 5, x_61);
lean_ctor_set_uint8(x_65, sizeof(void*)*6, x_53);
x_62 = x_65;
goto block_64;
}
block_64:
{
lean_object* x_63; 
x_63 = lean_st_ref_set(x_4, x_62);
lean_inc(x_6);
x_21 = x_4;
x_22 = x_6;
goto block_48;
}
}
}
block_48:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_12, 2);
x_24 = l_Lean_Compiler_LCNF_ToLCNF_applyToAny___redArg(x_23, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_20, x_12, x_25, x_22);
lean_dec(x_22);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; size_t x_28; size_t x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
x_28 = 1;
x_29 = lean_usize_add(x_2, x_28);
x_30 = lean_array_uset(x_19, x_2, x_27);
x_2 = x_29;
x_3 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_39; 
lean_dec_ref(x_19);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_26, 0);
x_39 = !lean_is_exclusive(x_26);
if (x_39 == 0)
{
x_33 = x_26;
x_34 = x_39;
goto block_38;
}
else
{
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_box(0);
x_34 = x_39;
goto block_38;
}
block_38:
{
lean_object* x_35; 
if (x_34 == 0)
{
x_35 = x_33;
goto block_36;
}
else
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_32);
x_35 = x_37;
goto block_36;
}
block_36:
{
return x_35;
}
}
}
}
else
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; uint8_t x_47; 
lean_dec(x_22);
lean_dec_ref(x_19);
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_40 = lean_ctor_get(x_24, 0);
x_47 = !lean_is_exclusive(x_24);
if (x_47 == 0)
{
x_41 = x_24;
x_42 = x_47;
goto block_46;
}
else
{
lean_inc(x_40);
lean_dec(x_24);
x_41 = lean_box(0);
x_42 = x_47;
goto block_46;
}
block_46:
{
lean_object* x_43; 
if (x_42 == 0)
{
x_43 = x_41;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_40);
x_43 = x_45;
goto block_44;
}
block_44:
{
return x_43;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_68 = lean_ctor_get(x_16, 0);
x_75 = !lean_is_exclusive(x_16);
if (x_75 == 0)
{
x_69 = x_16;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_16);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
else
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; uint8_t x_83; 
lean_dec(x_12);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_3);
x_76 = lean_ctor_get(x_14, 0);
x_83 = !lean_is_exclusive(x_14);
if (x_83 == 0)
{
x_77 = x_14;
x_78 = x_83;
goto block_82;
}
else
{
lean_inc(x_76);
lean_dec(x_14);
x_77 = lean_box(0);
x_78 = x_83;
goto block_82;
}
block_82:
{
lean_object* x_79; 
if (x_78 == 0)
{
x_79 = x_77;
goto block_80;
}
else
{
lean_object* x_81; 
x_81 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_81, 0, x_76);
x_79 = x_81;
goto block_80;
}
block_80:
{
return x_79;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___redArg(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__25___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_18; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
x_6 = x_1;
x_7 = x_18;
goto block_17;
}
else
{
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = x_18;
goto block_17;
}
block_17:
{
uint8_t x_8; 
x_8 = lean_nat_dec_lt(x_4, x_5);
if (x_8 == 0)
{
lean_del_object(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_4, x_9);
lean_inc_ref(x_3);
if (x_7 == 0)
{
lean_ctor_set(x_6, 1, x_10);
x_11 = x_6;
goto block_15;
}
else
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_10);
lean_ctor_set(x_16, 2, x_5);
x_11 = x_16;
goto block_15;
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
x_13 = lean_array_push(x_2, x_12);
x_1 = x_11;
x_2 = x_13;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = ((lean_object*)(l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27___closed__0));
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, lean_box(0));
return x_9;
}
}
LEAN_EXPORT lean_object* l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_expr_eqv(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__1(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_array_push(x_1, x_2);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_6, x_1);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_8);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_7);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_15 = lean_unsigned_to_nat(1u);
x_38 = l_Lean_instInhabitedExpr;
x_39 = lean_nat_add(x_2, x_6);
x_40 = lean_array_get_borrowed(x_38, x_3, x_39);
lean_dec(x_39);
lean_inc(x_40);
x_41 = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__1___boxed), 2, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = l_Array_findIdx_x3f_loop___redArg(x_41, x_4, x_42);
if (lean_obj_tag(x_43) == 1)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
x_45 = lean_nat_add(x_2, x_15);
x_46 = lean_nat_add(x_45, x_44);
lean_dec(x_44);
lean_dec(x_45);
x_47 = lean_array_get_borrowed(x_38, x_5, x_46);
lean_dec(x_46);
lean_inc(x_47);
x_48 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__0(x_7, x_47, x_8, x_9, x_10, x_11);
x_16 = x_48;
goto block_37;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_49 = l_Lean_Expr_fvarId_x21(x_40);
lean_inc_ref(x_8);
x_50 = l_Lean_FVarId_getType___redArg(x_49, x_8, x_10, x_11);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec_ref(x_50);
x_52 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_51);
x_53 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___lam__0(x_7, x_52, x_8, x_9, x_10, x_11);
x_16 = x_53;
goto block_37;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_61; 
lean_dec_ref(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
x_54 = lean_ctor_get(x_50, 0);
x_61 = !lean_is_exclusive(x_50);
if (x_61 == 0)
{
x_55 = x_50;
x_56 = x_61;
goto block_60;
}
else
{
lean_inc(x_54);
lean_dec(x_50);
x_55 = lean_box(0);
x_56 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_57; 
if (x_56 == 0)
{
x_57 = x_55;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_54);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
}
block_37:
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_28; 
x_17 = lean_ctor_get(x_16, 0);
x_28 = !lean_is_exclusive(x_16);
if (x_28 == 0)
{
x_18 = x_16;
x_19 = x_28;
goto block_27;
}
else
{
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = x_28;
goto block_27;
}
block_27:
{
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec_ref(x_8);
lean_dec(x_6);
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
lean_dec_ref(x_17);
if (x_19 == 0)
{
lean_ctor_set(x_18, 0, x_20);
x_21 = x_18;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_del_object(x_18);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
lean_dec_ref(x_17);
x_25 = lean_nat_add(x_6, x_15);
lean_dec(x_6);
x_6 = x_25;
x_7 = x_24;
goto _start;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec_ref(x_8);
lean_dec(x_6);
x_29 = lean_ctor_get(x_16, 0);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_30 = x_16;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_16);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__2));
x_2 = lean_unsigned_to_nat(12u);
x_3 = lean_unsigned_to_nat(597u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_24; 
x_13 = l_Lean_Expr_getAppFnArgs(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_24 = lean_name_eq(x_14, x_1);
lean_dec(x_14);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_25 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__3);
x_26 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__27(x_25, x_8, x_9, x_10, x_11);
return x_26;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_array_get_size(x_15);
x_28 = lean_nat_dec_le(x_4, x_3);
if (x_28 == 0)
{
lean_inc(x_4);
x_16 = x_4;
x_17 = x_27;
goto block_23;
}
else
{
lean_inc(x_3);
x_16 = x_3;
x_17 = x_27;
goto block_23;
}
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_mk_empty_array_with_capacity(x_2);
x_19 = l_Array_toSubarray___redArg(x_15, x_16, x_17);
x_20 = lean_mk_empty_array_with_capacity(x_3);
x_21 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__25___redArg(x_19, x_20);
x_22 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg(x_2, x_4, x_6, x_21, x_5, x_3, x_18, x_8, x_9, x_10, x_11);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_21);
lean_dec(x_4);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_st_ref_get(x_2);
x_5 = lean_ctor_get(x_4, 0);
lean_inc_ref(x_5);
lean_dec(x_4);
x_6 = l_Lean_Environment_getProjectionFnInfo_x3f(x_5, x_1);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___redArg(x_1, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28_spec__43___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_30; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_30 = !lean_is_exclusive(x_1);
if (x_30 == 0)
{
x_7 = x_1;
x_8 = x_30;
goto block_29;
}
else
{
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_5);
x_10 = lean_nat_dec_lt(x_2, x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_2);
x_11 = lean_array_push(x_5, x_3);
x_12 = lean_array_push(x_6, x_4);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_12);
lean_ctor_set(x_7, 0, x_11);
x_13 = x_7;
goto block_14;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_12);
x_13 = x_15;
goto block_14;
}
block_14:
{
return x_13;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_array_fget_borrowed(x_5, x_2);
x_17 = lean_expr_eqv(x_3, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
if (x_8 == 0)
{
x_18 = x_7;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
x_18 = x_23;
goto block_22;
}
block_22:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_2, x_19);
lean_dec(x_2);
x_1 = x_18;
x_2 = x_20;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_array_fset(x_5, x_2, x_3);
x_25 = lean_array_fset(x_6, x_2, x_4);
lean_dec(x_2);
if (x_8 == 0)
{
lean_ctor_set(x_7, 1, x_25);
lean_ctor_set(x_7, 0, x_24);
x_26 = x_7;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_25);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28_spec__43___redArg(x_1, x_4, x_2, x_3);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__2(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = 5;
x_8 = 1;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get_size(x_6);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_1;
}
else
{
lean_object* x_14; uint8_t x_15; uint8_t x_50; 
lean_inc_ref(x_6);
x_50 = !lean_is_exclusive(x_1);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_1, 0);
lean_dec(x_51);
x_14 = x_1;
x_15 = x_50;
goto block_49;
}
else
{
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = x_50;
goto block_49;
}
block_49:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_array_fget(x_6, x_11);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_6, x_11, x_17);
switch (lean_obj_tag(x_16)) {
case 0:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
x_36 = !lean_is_exclusive(x_16);
if (x_36 == 0)
{
x_27 = x_16;
x_28 = x_36;
goto block_35;
}
else
{
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_box(0);
x_28 = x_36;
goto block_35;
}
block_35:
{
uint8_t x_29; 
x_29 = lean_expr_eqv(x_4, x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_del_object(x_27);
x_30 = l_Lean_PersistentHashMap_mkCollisionNode___redArg(x_25, x_26, x_4, x_5);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_19 = x_31;
goto block_24;
}
else
{
lean_object* x_32; 
lean_dec(x_26);
lean_dec(x_25);
if (x_28 == 0)
{
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 0, x_4);
x_32 = x_27;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_5);
x_32 = x_34;
goto block_33;
}
block_33:
{
x_19 = x_32;
goto block_24;
}
}
}
}
case 1:
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_47; 
x_37 = lean_ctor_get(x_16, 0);
x_47 = !lean_is_exclusive(x_16);
if (x_47 == 0)
{
x_38 = x_16;
x_39 = x_47;
goto block_46;
}
else
{
lean_inc(x_37);
lean_dec(x_16);
x_38 = lean_box(0);
x_39 = x_47;
goto block_46;
}
block_46:
{
size_t x_40; size_t x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_usize_shift_right(x_2, x_7);
x_41 = lean_usize_add(x_3, x_8);
x_42 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg(x_37, x_40, x_41, x_4, x_5);
if (x_39 == 0)
{
lean_ctor_set(x_38, 0, x_42);
x_43 = x_38;
goto block_44;
}
else
{
lean_object* x_45; 
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_42);
x_43 = x_45;
goto block_44;
}
block_44:
{
x_19 = x_43;
goto block_24;
}
}
}
default: 
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_4);
lean_ctor_set(x_48, 1, x_5);
x_19 = x_48;
goto block_24;
}
}
block_24:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_array_fset(x_18, x_11, x_19);
lean_dec(x_11);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
x_73 = !lean_is_exclusive(x_1);
if (x_73 == 0)
{
x_54 = x_1;
x_55 = x_73;
goto block_72;
}
else
{
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = lean_box(0);
x_55 = x_73;
goto block_72;
}
block_72:
{
lean_object* x_56; 
if (x_55 == 0)
{
x_56 = x_54;
goto block_70;
}
else
{
lean_object* x_71; 
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_52);
lean_ctor_set(x_71, 1, x_53);
x_56 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_57; uint8_t x_58; size_t x_65; uint8_t x_66; 
x_57 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28___redArg(x_56, x_4, x_5);
x_65 = 7;
x_66 = lean_usize_dec_le(x_65, x_3);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(x_57);
x_68 = lean_unsigned_to_nat(4u);
x_69 = lean_nat_dec_lt(x_67, x_68);
lean_dec(x_67);
x_58 = x_69;
goto block_64;
}
else
{
x_58 = x_66;
goto block_64;
}
block_64:
{
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_57, 0);
lean_inc_ref(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc_ref(x_60);
lean_dec_ref(x_57);
x_61 = lean_unsigned_to_nat(0u);
x_62 = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__2, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__2_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__2);
x_63 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___redArg(x_3, x_59, x_60, x_61, x_62);
lean_dec_ref(x_60);
lean_dec_ref(x_59);
return x_63;
}
else
{
return x_57;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___redArg(size_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_2);
x_7 = lean_nat_dec_lt(x_4, x_6);
if (x_7 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; size_t x_11; size_t x_12; lean_object* x_13; size_t x_14; size_t x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_8 = lean_array_fget_borrowed(x_2, x_4);
x_9 = lean_array_fget_borrowed(x_3, x_4);
x_10 = l_Lean_Expr_hash(x_8);
x_11 = lean_uint64_to_usize(x_10);
x_12 = 5;
x_13 = lean_unsigned_to_nat(1u);
x_14 = 1;
x_15 = lean_usize_sub(x_1, x_14);
x_16 = lean_usize_mul(x_12, x_15);
x_17 = lean_usize_shift_right(x_11, x_16);
x_18 = lean_nat_add(x_4, x_13);
lean_dec(x_4);
lean_inc(x_9);
lean_inc(x_8);
x_19 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg(x_5, x_17, x_1, x_8, x_9);
x_4 = x_18;
x_5 = x_19;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; lean_object* x_7; 
x_6 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_7 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg(x_1, x_6, x_7, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; size_t x_5; size_t x_6; lean_object* x_7; 
x_4 = l_Lean_Expr_hash(x_2);
x_5 = lean_uint64_to_usize(x_4);
x_6 = 1;
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg(x_1, x_5, x_6, x_2, x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_array_get_size(x_1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_array_fget_borrowed(x_1, x_3);
x_9 = lean_expr_eqv(x_4, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_3, x_10);
lean_dec(x_3);
x_3 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_fget_borrowed(x_2, x_3);
lean_dec(x_3);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___redArg(x_1, x_2, x_3, x_4);
lean_dec_ref(x_4);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_25; 
x_4 = lean_ctor_get(x_1, 0);
x_25 = !lean_is_exclusive(x_1);
if (x_25 == 0)
{
x_5 = x_1;
x_6 = x_25;
goto block_24;
}
else
{
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_box(0);
x_6 = x_25;
goto block_24;
}
block_24:
{
lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_box(2);
x_8 = 5;
x_9 = lean_usize_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg___closed__1);
x_10 = lean_usize_land(x_2, x_9);
x_11 = lean_usize_to_nat(x_10);
x_12 = lean_array_get(x_7, x_4, x_11);
lean_dec(x_11);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_12)) {
case 0:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec_ref(x_12);
x_15 = lean_expr_eqv(x_3, x_13);
lean_dec(x_13);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_del_object(x_5);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; 
if (x_6 == 0)
{
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_14);
x_17 = x_5;
goto block_18;
}
else
{
lean_object* x_19; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_17 = x_19;
goto block_18;
}
block_18:
{
return x_17;
}
}
}
case 1:
{
lean_object* x_20; size_t x_21; 
lean_del_object(x_5);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec_ref(x_12);
x_21 = lean_usize_shift_right(x_2, x_8);
x_1 = x_20;
x_2 = x_21;
goto _start;
}
default: 
{
lean_object* x_23; 
lean_del_object(x_5);
x_23 = lean_box(0);
return x_23;
}
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_27);
lean_dec_ref(x_1);
x_28 = lean_unsigned_to_nat(0u);
x_29 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___redArg(x_26, x_27, x_28, x_3);
lean_dec_ref(x_27);
lean_dec_ref(x_26);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; lean_object* x_5; 
x_3 = l_Lean_Expr_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = l_Lean_Expr_sort___override(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
x_12 = lean_nat_dec_lt(x_11, x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec_ref(x_1);
x_13 = lean_box(x_4);
x_14 = lean_apply_7(x_3, x_13, x_5, x_6, x_7, x_8, x_9, lean_box(0));
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec_ref(x_3);
x_15 = lean_nat_sub(x_2, x_11);
lean_dec(x_11);
lean_inc(x_9);
lean_inc_ref(x_8);
x_16 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_1, x_15, x_5, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_17, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_19 = lean_ctor_get(x_16, 0);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
x_20 = x_16;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_10 = l_Lean_instInhabitedExpr;
x_11 = lean_unsigned_to_nat(5u);
x_12 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_13 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_13);
x_14 = lean_mk_array(x_13, x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_13, x_15);
lean_dec(x_13);
lean_inc_ref(x_1);
x_17 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_14, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get(x_10, x_17, x_18);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_19);
x_21 = lean_array_get(x_10, x_17, x_15);
x_22 = l_Lean_Compiler_LCNF_ToLCNF_mkLcProof(x_21);
x_23 = lean_array_get(x_10, x_17, x_2);
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_mk_empty_array_with_capacity(x_24);
x_26 = lean_array_push(x_25, x_20);
x_27 = lean_array_push(x_26, x_22);
x_28 = l_Lean_Expr_beta(x_23, x_27);
x_29 = lean_array_get_size(x_17);
x_30 = l_Array_toSubarray___redArg(x_17, x_11, x_29);
x_31 = l_Subarray_copy___redArg(x_30);
x_32 = l_Lean_mkAppN(x_28, x_31);
lean_dec_ref(x_31);
x_33 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit___boxed), 8, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_11, x_33, x_3, x_4, x_5, x_6, x_7, x_8);
return x_34;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_63; lean_object* x_64; 
x_63 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_63 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_93 = lean_st_ref_get(x_3);
x_94 = lean_ctor_get(x_93, 0);
lean_inc_ref(x_94);
lean_dec(x_93);
x_95 = lean_box(1);
x_96 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_97 = lean_unsigned_to_nat(0u);
x_98 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_99 = lean_box(0);
x_100 = 1;
x_101 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_101, 0, x_96);
lean_ctor_set(x_101, 1, x_95);
lean_ctor_set(x_101, 2, x_94);
lean_ctor_set(x_101, 3, x_98);
lean_ctor_set(x_101, 4, x_99);
lean_ctor_set(x_101, 5, x_97);
lean_ctor_set(x_101, 6, x_99);
lean_ctor_set_uint8(x_101, sizeof(void*)*7, x_63);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 1, x_63);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 2, x_63);
lean_ctor_set_uint8(x_101, sizeof(void*)*7 + 3, x_100);
x_102 = lean_unsigned_to_nat(32u);
x_103 = lean_mk_empty_array_with_capacity(x_102);
lean_dec_ref(x_103);
x_104 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_105 = lean_st_mk_ref(x_104);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_105);
lean_inc_ref(x_1);
x_106 = lean_infer_type(x_1, x_101, x_105, x_6, x_7);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
lean_dec_ref(x_106);
x_108 = lean_st_ref_get(x_105);
lean_dec(x_105);
lean_dec(x_108);
x_64 = x_107;
goto block_92;
}
else
{
lean_dec(x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_106, 0);
lean_inc(x_109);
lean_dec_ref(x_106);
x_64 = x_109;
goto block_92;
}
else
{
lean_object* x_110; lean_object* x_111; uint8_t x_112; uint8_t x_117; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_110 = lean_ctor_get(x_106, 0);
x_117 = !lean_is_exclusive(x_106);
if (x_117 == 0)
{
x_111 = x_106;
x_112 = x_117;
goto block_116;
}
else
{
lean_inc(x_110);
lean_dec(x_106);
x_111 = lean_box(0);
x_112 = x_117;
goto block_116;
}
block_116:
{
lean_object* x_113; 
if (x_112 == 0)
{
x_113 = x_111;
goto block_114;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_115, 0, x_110);
x_113 = x_115;
goto block_114;
}
block_114:
{
return x_113;
}
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_118 = lean_box(0);
x_119 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_119, 0, x_118);
return x_119;
}
block_62:
{
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc_ref(x_9);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_9, x_3, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec_ref(x_9);
x_14 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_5);
lean_dec_ref(x_4);
lean_inc(x_7);
lean_inc_ref(x_6);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_9, x_3, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_43; 
x_16 = lean_ctor_get(x_15, 0);
x_43 = !lean_is_exclusive(x_15);
if (x_43 == 0)
{
x_17 = x_15;
x_18 = x_43;
goto block_42;
}
else
{
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = x_43;
goto block_42;
}
block_42:
{
uint8_t x_19; 
x_19 = l_Lean_Compiler_LCNF_isPredicateType(x_16);
if (x_19 == 0)
{
lean_object* x_20; 
lean_del_object(x_17);
x_20 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_1, x_3, x_6, x_7);
lean_dec(x_3);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_29; 
x_21 = lean_ctor_get(x_20, 0);
x_29 = !lean_is_exclusive(x_20);
if (x_29 == 0)
{
x_22 = x_20;
x_23 = x_29;
goto block_28;
}
else
{
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_box(0);
x_23 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_24, 0, x_21);
if (x_23 == 0)
{
lean_ctor_set(x_22, 0, x_24);
x_25 = x_22;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_37; 
x_30 = lean_ctor_get(x_20, 0);
x_37 = !lean_is_exclusive(x_20);
if (x_37 == 0)
{
x_31 = x_20;
x_32 = x_37;
goto block_36;
}
else
{
lean_inc(x_30);
lean_dec(x_20);
x_31 = lean_box(0);
x_32 = x_37;
goto block_36;
}
block_36:
{
lean_object* x_33; 
if (x_32 == 0)
{
x_33 = x_31;
goto block_34;
}
else
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_30);
x_33 = x_35;
goto block_34;
}
block_34:
{
return x_33;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_38 = lean_box(0);
if (x_18 == 0)
{
lean_ctor_set(x_17, 0, x_38);
x_39 = x_17;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_39 = x_41;
goto block_40;
}
block_40:
{
return x_39;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_3);
lean_dec_ref(x_1);
x_44 = lean_ctor_get(x_15, 0);
x_51 = !lean_is_exclusive(x_15);
if (x_51 == 0)
{
x_45 = x_15;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_15);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_52 = lean_ctor_get(x_11, 0);
x_59 = !lean_is_exclusive(x_11);
if (x_59 == 0)
{
x_53 = x_11;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_11);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
return x_61;
}
}
block_92:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_65 = lean_st_ref_get(x_3);
x_66 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_66);
lean_dec(x_65);
x_67 = lean_box(1);
x_68 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_69 = lean_unsigned_to_nat(0u);
x_70 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_71 = lean_box(0);
x_72 = 1;
x_73 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_67);
lean_ctor_set(x_73, 2, x_66);
lean_ctor_set(x_73, 3, x_70);
lean_ctor_set(x_73, 4, x_71);
lean_ctor_set(x_73, 5, x_69);
lean_ctor_set(x_73, 6, x_71);
lean_ctor_set_uint8(x_73, sizeof(void*)*7, x_63);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 1, x_63);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 2, x_63);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 3, x_72);
x_74 = lean_unsigned_to_nat(32u);
x_75 = lean_mk_empty_array_with_capacity(x_74);
lean_dec_ref(x_75);
x_76 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_77 = lean_st_mk_ref(x_76);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_77);
lean_inc_ref(x_64);
x_78 = l_Lean_Meta_isProp(x_64, x_73, x_77, x_6, x_7);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
lean_dec_ref(x_78);
x_80 = lean_st_ref_get(x_77);
lean_dec(x_77);
lean_dec(x_80);
x_81 = lean_unbox(x_79);
lean_dec(x_79);
x_9 = x_64;
x_10 = x_81;
goto block_62;
}
else
{
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_82; uint8_t x_83; 
x_82 = lean_ctor_get(x_78, 0);
lean_inc(x_82);
lean_dec_ref(x_78);
x_83 = lean_unbox(x_82);
lean_dec(x_82);
x_9 = x_64;
x_10 = x_83;
goto block_62;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_91; 
lean_dec_ref(x_64);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_84 = lean_ctor_get(x_78, 0);
x_91 = !lean_is_exclusive(x_78);
if (x_91 == 0)
{
x_85 = x_78;
x_86 = x_91;
goto block_90;
}
else
{
lean_inc(x_84);
lean_dec(x_78);
x_85 = lean_box(0);
x_86 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_87; 
if (x_86 == 0)
{
x_87 = x_85;
goto block_88;
}
else
{
lean_object* x_89; 
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_84);
x_87 = x_89;
goto block_88;
}
block_88:
{
return x_87;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget_borrowed(x_2, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_14);
x_15 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_array_push(x_4, x_16);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_3 = x_19;
x_4 = x_17;
goto _start;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; uint8_t x_28; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_15, 0);
x_28 = !lean_is_exclusive(x_15);
if (x_28 == 0)
{
x_22 = x_15;
x_23 = x_28;
goto block_27;
}
else
{
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(0);
x_23 = x_28;
goto block_27;
}
block_27:
{
lean_object* x_24; 
if (x_23 == 0)
{
x_24 = x_22;
goto block_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_21);
x_24 = x_26;
goto block_25;
}
block_25:
{
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_array_get_size(x_2);
x_12 = lean_nat_dec_eq(x_11, x_3);
if (x_12 == 0)
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec_ref(x_1);
x_14 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg___closed__0));
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___redArg(x_11, x_2, x_3, x_14, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
x_19 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_17, x_18, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_27; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_20 = lean_ctor_get(x_15, 0);
x_27 = !lean_is_exclusive(x_15);
if (x_27 == 0)
{
x_21 = x_15;
x_22 = x_27;
goto block_26;
}
else
{
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_box(0);
x_22 = x_27;
goto block_26;
}
block_26:
{
lean_object* x_23; 
if (x_22 == 0)
{
x_23 = x_21;
goto block_24;
}
else
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_23 = x_25;
goto block_24;
}
block_24:
{
return x_23;
}
}
}
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_28);
return x_29;
}
}
else
{
lean_object* x_30; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_1);
return x_30;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_116; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_116 = !lean_is_exclusive(x_1);
if (x_116 == 0)
{
x_12 = x_1;
x_13 = x_116;
goto block_115;
}
else
{
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = x_116;
goto block_115;
}
block_115:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_77; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_11);
x_77 = l_Lean_Compiler_LCNF_ToLCNF_visitBoundedLambda___redArg(x_2, x_11, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_array_get_size(x_79);
x_82 = lean_nat_dec_lt(x_81, x_11);
if (x_82 == 0)
{
lean_dec(x_11);
x_14 = x_79;
x_15 = x_80;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_76;
}
else
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_nat_sub(x_11, x_81);
lean_dec(x_11);
lean_inc(x_8);
lean_inc_ref(x_7);
x_84 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_80, x_83, x_4, x_7, x_8);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
lean_dec_ref(x_84);
lean_inc(x_8);
lean_inc_ref(x_7);
x_86 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg(x_85, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Array_append___redArg(x_79, x_88);
lean_dec(x_88);
x_14 = x_90;
x_15 = x_89;
x_16 = x_3;
x_17 = x_4;
x_18 = x_5;
x_19 = x_6;
x_20 = x_7;
x_21 = x_8;
goto block_76;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_dec(x_79);
lean_del_object(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_91 = lean_ctor_get(x_86, 0);
x_98 = !lean_is_exclusive(x_86);
if (x_98 == 0)
{
x_92 = x_86;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_86);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; uint8_t x_106; 
lean_dec(x_79);
lean_del_object(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_99 = lean_ctor_get(x_84, 0);
x_106 = !lean_is_exclusive(x_84);
if (x_106 == 0)
{
x_100 = x_84;
x_101 = x_106;
goto block_105;
}
else
{
lean_inc(x_99);
lean_dec(x_84);
x_100 = lean_box(0);
x_101 = x_106;
goto block_105;
}
block_105:
{
lean_object* x_102; 
if (x_101 == 0)
{
x_102 = x_100;
goto block_103;
}
else
{
lean_object* x_104; 
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_99);
x_102 = x_104;
goto block_103;
}
block_103:
{
return x_102;
}
}
}
}
}
else
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; uint8_t x_114; 
lean_del_object(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_107 = lean_ctor_get(x_77, 0);
x_114 = !lean_is_exclusive(x_77);
if (x_114 == 0)
{
x_108 = x_77;
x_109 = x_114;
goto block_113;
}
else
{
lean_inc(x_107);
lean_dec(x_77);
x_108 = lean_box(0);
x_109 = x_114;
goto block_113;
}
block_113:
{
lean_object* x_110; 
if (x_109 == 0)
{
x_110 = x_108;
goto block_111;
}
else
{
lean_object* x_112; 
x_112 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_112, 0, x_107);
x_110 = x_112;
goto block_111;
}
block_111:
{
return x_110;
}
}
}
block_76:
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_array_size(x_14);
x_23 = 0;
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
x_24 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___redArg(x_22, x_23, x_14, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
lean_inc(x_17);
x_26 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_15, x_16, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc(x_21);
lean_inc_ref(x_20);
lean_inc(x_19);
lean_inc_ref(x_18);
x_28 = l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg(x_27, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_17);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
x_30 = 0;
lean_inc(x_29);
x_31 = l_Lean_Compiler_LCNF_Code_inferType(x_30, x_29, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; uint8_t x_43; 
x_32 = lean_ctor_get(x_31, 0);
x_43 = !lean_is_exclusive(x_31);
if (x_43 == 0)
{
x_33 = x_31;
x_34 = x_43;
goto block_42;
}
else
{
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_10);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_29);
if (x_13 == 0)
{
lean_ctor_set(x_12, 1, x_35);
lean_ctor_set(x_12, 0, x_32);
x_36 = x_12;
goto block_40;
}
else
{
lean_object* x_41; 
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_32);
lean_ctor_set(x_41, 1, x_35);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_34 == 0)
{
lean_ctor_set(x_33, 0, x_36);
x_37 = x_33;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_36);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_51; 
lean_dec(x_29);
lean_dec(x_25);
lean_del_object(x_12);
lean_dec(x_10);
x_44 = lean_ctor_get(x_31, 0);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
x_45 = x_31;
x_46 = x_51;
goto block_50;
}
else
{
lean_inc(x_44);
lean_dec(x_31);
x_45 = lean_box(0);
x_46 = x_51;
goto block_50;
}
block_50:
{
lean_object* x_47; 
if (x_46 == 0)
{
x_47 = x_45;
goto block_48;
}
else
{
lean_object* x_49; 
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_44);
x_47 = x_49;
goto block_48;
}
block_48:
{
return x_47;
}
}
}
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_59; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_del_object(x_12);
lean_dec(x_10);
x_52 = lean_ctor_get(x_28, 0);
x_59 = !lean_is_exclusive(x_28);
if (x_59 == 0)
{
x_53 = x_28;
x_54 = x_59;
goto block_58;
}
else
{
lean_inc(x_52);
lean_dec(x_28);
x_53 = lean_box(0);
x_54 = x_59;
goto block_58;
}
block_58:
{
lean_object* x_55; 
if (x_54 == 0)
{
x_55 = x_53;
goto block_56;
}
else
{
lean_object* x_57; 
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_52);
x_55 = x_57;
goto block_56;
}
block_56:
{
return x_55;
}
}
}
}
else
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_67; 
lean_dec(x_25);
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_del_object(x_12);
lean_dec(x_10);
x_60 = lean_ctor_get(x_26, 0);
x_67 = !lean_is_exclusive(x_26);
if (x_67 == 0)
{
x_61 = x_26;
x_62 = x_67;
goto block_66;
}
else
{
lean_inc(x_60);
lean_dec(x_26);
x_61 = lean_box(0);
x_62 = x_67;
goto block_66;
}
block_66:
{
lean_object* x_63; 
if (x_62 == 0)
{
x_63 = x_61;
goto block_64;
}
else
{
lean_object* x_65; 
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_63 = x_65;
goto block_64;
}
block_64:
{
return x_63;
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; uint8_t x_70; uint8_t x_75; 
lean_dec(x_21);
lean_dec_ref(x_20);
lean_dec(x_19);
lean_dec_ref(x_18);
lean_dec(x_17);
lean_dec_ref(x_15);
lean_del_object(x_12);
lean_dec(x_10);
x_68 = lean_ctor_get(x_24, 0);
x_75 = !lean_is_exclusive(x_24);
if (x_75 == 0)
{
x_69 = x_24;
x_70 = x_75;
goto block_74;
}
else
{
lean_inc(x_68);
lean_dec(x_24);
x_69 = lean_box(0);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
if (x_70 == 0)
{
x_71 = x_69;
goto block_72;
}
else
{
lean_object* x_73; 
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_68);
x_71 = x_73;
goto block_72;
}
block_72:
{
return x_71;
}
}
}
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_166; 
x_117 = lean_ctor_get(x_1, 0);
x_166 = !lean_is_exclusive(x_1);
if (x_166 == 0)
{
x_118 = x_1;
x_119 = x_166;
goto block_165;
}
else
{
lean_inc(x_117);
lean_dec(x_1);
x_118 = lean_box(0);
x_119 = x_166;
goto block_165;
}
block_165:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = l_Lean_Compiler_LCNF_erasedExpr;
x_121 = lean_mk_array(x_117, x_120);
x_122 = l_Lean_mkAppN(x_2, x_121);
lean_dec_ref(x_121);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_123 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_122, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
lean_dec_ref(x_123);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_125 = l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg(x_124, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; uint8_t x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
lean_dec_ref(x_125);
x_127 = 0;
lean_inc(x_126);
x_128 = l_Lean_Compiler_LCNF_Code_inferType(x_127, x_126, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_140; 
x_129 = lean_ctor_get(x_128, 0);
x_140 = !lean_is_exclusive(x_128);
if (x_140 == 0)
{
x_130 = x_128;
x_131 = x_140;
goto block_139;
}
else
{
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_box(0);
x_131 = x_140;
goto block_139;
}
block_139:
{
lean_object* x_132; 
if (x_119 == 0)
{
lean_ctor_set_tag(x_118, 2);
lean_ctor_set(x_118, 0, x_126);
x_132 = x_118;
goto block_137;
}
else
{
lean_object* x_138; 
x_138 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_138, 0, x_126);
x_132 = x_138;
goto block_137;
}
block_137:
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_132);
if (x_131 == 0)
{
lean_ctor_set(x_130, 0, x_133);
x_134 = x_130;
goto block_135;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_136, 0, x_133);
x_134 = x_136;
goto block_135;
}
block_135:
{
return x_134;
}
}
}
}
else
{
lean_object* x_141; lean_object* x_142; uint8_t x_143; uint8_t x_148; 
lean_dec(x_126);
lean_del_object(x_118);
x_141 = lean_ctor_get(x_128, 0);
x_148 = !lean_is_exclusive(x_128);
if (x_148 == 0)
{
x_142 = x_128;
x_143 = x_148;
goto block_147;
}
else
{
lean_inc(x_141);
lean_dec(x_128);
x_142 = lean_box(0);
x_143 = x_148;
goto block_147;
}
block_147:
{
lean_object* x_144; 
if (x_143 == 0)
{
x_144 = x_142;
goto block_145;
}
else
{
lean_object* x_146; 
x_146 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_146, 0, x_141);
x_144 = x_146;
goto block_145;
}
block_145:
{
return x_144;
}
}
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; uint8_t x_156; 
lean_del_object(x_118);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_149 = lean_ctor_get(x_125, 0);
x_156 = !lean_is_exclusive(x_125);
if (x_156 == 0)
{
x_150 = x_125;
x_151 = x_156;
goto block_155;
}
else
{
lean_inc(x_149);
lean_dec(x_125);
x_150 = lean_box(0);
x_151 = x_156;
goto block_155;
}
block_155:
{
lean_object* x_152; 
if (x_151 == 0)
{
x_152 = x_150;
goto block_153;
}
else
{
lean_object* x_154; 
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_149);
x_152 = x_154;
goto block_153;
}
block_153:
{
return x_152;
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; uint8_t x_159; uint8_t x_164; 
lean_del_object(x_118);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_157 = lean_ctor_get(x_123, 0);
x_164 = !lean_is_exclusive(x_123);
if (x_164 == 0)
{
x_158 = x_123;
x_159 = x_164;
goto block_163;
}
else
{
lean_inc(x_157);
lean_dec(x_123);
x_158 = lean_box(0);
x_159 = x_164;
goto block_163;
}
block_163:
{
lean_object* x_160; 
if (x_159 == 0)
{
x_160 = x_158;
goto block_161;
}
else
{
lean_object* x_162; 
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_157);
x_160 = x_162;
goto block_161;
}
block_161:
{
return x_160;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___lam__0___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_2);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_nat_dec_lt(x_3, x_1);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_78; 
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 0);
x_78 = !lean_is_exclusive(x_4);
if (x_78 == 0)
{
lean_object* x_79; 
x_79 = lean_ctor_get(x_4, 1);
lean_dec(x_79);
x_17 = x_4;
x_18 = x_78;
goto block_77;
}
else
{
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_box(0);
x_18 = x_78;
goto block_77;
}
block_77:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_75; 
x_19 = lean_ctor_get(x_14, 0);
x_75 = !lean_is_exclusive(x_14);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_14, 1);
lean_dec(x_76);
x_20 = x_14;
x_21 = x_75;
goto block_74;
}
else
{
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_box(0);
x_21 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_15, 0);
x_23 = lean_ctor_get(x_15, 1);
x_24 = lean_ctor_get(x_15, 2);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
if (x_21 == 0)
{
x_26 = x_20;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_19);
lean_ctor_set(x_32, 1, x_15);
x_26 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_27; 
if (x_18 == 0)
{
lean_ctor_set(x_17, 1, x_26);
x_27 = x_17;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_16);
lean_ctor_set(x_30, 1, x_26);
x_27 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
return x_28;
}
}
}
else
{
lean_object* x_33; uint8_t x_34; uint8_t x_70; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc_ref(x_22);
lean_del_object(x_17);
x_70 = !lean_is_exclusive(x_15);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_15, 2);
lean_dec(x_71);
x_72 = lean_ctor_get(x_15, 1);
lean_dec(x_72);
x_73 = lean_ctor_get(x_15, 0);
lean_dec(x_73);
x_33 = x_15;
x_34 = x_70;
goto block_69;
}
else
{
lean_dec(x_15);
x_33 = lean_box(0);
x_34 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = l_Lean_instInhabitedExpr;
x_36 = lean_array_fget_borrowed(x_22, x_23);
x_37 = lean_array_get_borrowed(x_35, x_2, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc(x_37);
lean_inc(x_36);
x_38 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_36, x_37, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_60; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
lean_dec_ref(x_38);
x_40 = lean_ctor_get(x_39, 0);
x_41 = lean_ctor_get(x_39, 1);
x_60 = !lean_is_exclusive(x_39);
if (x_60 == 0)
{
x_42 = x_39;
x_43 = x_60;
goto block_59;
}
else
{
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = x_60;
goto block_59;
}
block_59:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_add(x_23, x_44);
lean_dec(x_23);
if (x_34 == 0)
{
lean_ctor_set(x_33, 1, x_45);
x_46 = x_33;
goto block_57;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_58, 0, x_22);
lean_ctor_set(x_58, 1, x_45);
lean_ctor_set(x_58, 2, x_24);
x_46 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Lean_Compiler_LCNF_joinTypes(x_40, x_16);
x_48 = lean_array_push(x_19, x_41);
if (x_43 == 0)
{
lean_ctor_set(x_42, 1, x_46);
lean_ctor_set(x_42, 0, x_48);
x_49 = x_42;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_46);
x_49 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_50; 
if (x_21 == 0)
{
lean_ctor_set(x_20, 1, x_49);
lean_ctor_set(x_20, 0, x_47);
x_50 = x_20;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_49);
x_50 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_51; 
x_51 = lean_nat_add(x_3, x_44);
lean_dec(x_3);
x_3 = x_51;
x_4 = x_50;
goto _start;
}
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_del_object(x_33);
lean_dec(x_24);
lean_dec(x_23);
lean_dec_ref(x_22);
lean_del_object(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_61 = lean_ctor_get(x_38, 0);
x_68 = !lean_is_exclusive(x_38);
if (x_68 == 0)
{
x_62 = x_38;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_38);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1);
x_2 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__1);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_1);
lean_ctor_set(x_3, 4, x_1);
lean_ctor_set(x_3, 5, x_1);
lean_ctor_set(x_3, 6, x_1);
lean_ctor_set(x_3, 7, x_1);
lean_ctor_set(x_3, 8, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__2, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__2_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__2);
x_2 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__3);
x_3 = lean_box(1);
x_4 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__1, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__1);
x_5 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__0);
x_6 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_2);
lean_ctor_set(x_6, 4, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__4));
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(589u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(66u);
x_3 = lean_unsigned_to_nat(593u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(64u);
x_3 = lean_unsigned_to_nat(592u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__8(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(55u);
x_3 = lean_unsigned_to_nat(584u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__1));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_17; lean_object* x_26; 
lean_inc(x_15);
lean_inc_ref(x_14);
x_26 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_9, x_11, x_14, x_15);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec_ref(x_26);
lean_inc_ref(x_14);
lean_inc(x_1);
x_28 = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17(x_1, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
lean_dec_ref(x_28);
if (lean_obj_tag(x_29) == 5)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; uint8_t x_189; 
x_30 = lean_ctor_get(x_29, 0);
x_189 = !lean_is_exclusive(x_29);
if (x_189 == 0)
{
x_31 = x_29;
x_32 = x_189;
goto block_188;
}
else
{
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = x_189;
goto block_188;
}
block_188:
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = l_CasesInfo_numAlts(x_2);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_nat_dec_eq(x_33, x_34);
if (x_35 == 0)
{
uint8_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; lean_object* x_172; lean_object* x_173; 
x_104 = 1;
x_105 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_106 = lean_box(1);
x_107 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4, &l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4_once, _init_l_Lean_Compiler_LCNF_ToLCNF_run___redArg___closed__4);
x_108 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_109 = lean_box(0);
x_110 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_110, 0, x_105);
lean_ctor_set(x_110, 1, x_106);
lean_ctor_set(x_110, 2, x_107);
lean_ctor_set(x_110, 3, x_108);
lean_ctor_set(x_110, 4, x_109);
lean_ctor_set(x_110, 5, x_34);
lean_ctor_set(x_110, 6, x_109);
lean_ctor_set_uint8(x_110, sizeof(void*)*7, x_35);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 1, x_35);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 2, x_35);
lean_ctor_set_uint8(x_110, sizeof(void*)*7 + 3, x_104);
x_111 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__3, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__3_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__3);
x_172 = lean_st_mk_ref(x_111);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_172);
lean_inc_ref(x_110);
lean_inc_ref(x_30);
x_173 = l_Lean_Meta_isInductivePredicateVal(x_30, x_110, x_172, x_14, x_15);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; uint8_t x_176; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
lean_dec_ref(x_173);
x_175 = lean_st_ref_get(x_172);
lean_dec(x_172);
lean_dec(x_175);
x_176 = lean_unbox(x_174);
lean_dec(x_174);
x_112 = x_176;
goto block_171;
}
else
{
lean_dec(x_172);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = lean_ctor_get(x_173, 0);
lean_inc(x_177);
lean_dec_ref(x_173);
x_178 = lean_unbox(x_177);
lean_dec(x_177);
x_112 = x_178;
goto block_171;
}
else
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_186; 
lean_dec_ref(x_110);
lean_dec(x_33);
lean_del_object(x_31);
lean_dec_ref(x_30);
lean_dec(x_27);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_179 = lean_ctor_get(x_173, 0);
x_186 = !lean_is_exclusive(x_173);
if (x_186 == 0)
{
x_180 = x_173;
x_181 = x_186;
goto block_185;
}
else
{
lean_inc(x_179);
lean_dec(x_173);
x_180 = lean_box(0);
x_181 = x_186;
goto block_185;
}
block_185:
{
lean_object* x_182; 
if (x_181 == 0)
{
x_182 = x_180;
goto block_183;
}
else
{
lean_object* x_184; 
x_184 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_184, 0, x_179);
x_182 = x_184;
goto block_183;
}
block_183:
{
return x_182;
}
}
}
}
block_171:
{
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec_ref(x_110);
lean_dec(x_33);
lean_dec_ref(x_30);
x_113 = l_Lean_instInhabitedExpr;
x_114 = lean_array_get_borrowed(x_113, x_4, x_7);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
lean_inc(x_114);
x_115 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_114, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
lean_dec_ref(x_115);
if (lean_obj_tag(x_116) == 1)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec_ref(x_116);
x_36 = x_108;
x_37 = x_117;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_15;
goto block_103;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_116);
x_118 = lean_box(1);
x_119 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
x_120 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg(x_118, x_119, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
lean_dec_ref(x_120);
x_36 = x_108;
x_37 = x_121;
x_38 = x_10;
x_39 = x_11;
x_40 = x_12;
x_41 = x_13;
x_42 = x_14;
x_43 = x_15;
goto block_103;
}
else
{
lean_object* x_122; lean_object* x_123; uint8_t x_124; uint8_t x_129; 
lean_del_object(x_31);
lean_dec(x_27);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_122 = lean_ctor_get(x_120, 0);
x_129 = !lean_is_exclusive(x_120);
if (x_129 == 0)
{
x_123 = x_120;
x_124 = x_129;
goto block_128;
}
else
{
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_box(0);
x_124 = x_129;
goto block_128;
}
block_128:
{
lean_object* x_125; 
if (x_124 == 0)
{
x_125 = x_123;
goto block_126;
}
else
{
lean_object* x_127; 
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_122);
x_125 = x_127;
goto block_126;
}
block_126:
{
return x_125;
}
}
}
}
}
else
{
lean_del_object(x_31);
lean_dec(x_27);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
return x_115;
}
}
else
{
uint8_t x_130; 
lean_del_object(x_31);
lean_dec(x_27);
x_130 = lean_nat_dec_eq(x_33, x_8);
lean_dec(x_33);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
lean_dec_ref(x_110);
lean_dec_ref(x_30);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_131 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__5, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__5_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__5);
x_132 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_131, x_10, x_11, x_12, x_13, x_14, x_15);
return x_132;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_30, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_30, 4);
lean_inc(x_134);
lean_dec_ref(x_30);
x_135 = lean_box(0);
x_136 = l_List_get_x21Internal___redArg(x_135, x_134, x_34);
lean_dec(x_134);
lean_inc_ref(x_14);
x_137 = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17(x_136, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
lean_dec_ref(x_137);
if (lean_obj_tag(x_138) == 6)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc_ref(x_139);
lean_dec_ref(x_138);
x_140 = l_instInhabitedCasesAltInfo_default;
x_141 = lean_array_get(x_140, x_6, x_34);
lean_dec_ref(x_6);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec_ref(x_141);
x_143 = lean_st_mk_ref(x_111);
x_144 = lean_ctor_get(x_139, 0);
lean_inc_ref(x_144);
lean_dec_ref(x_139);
x_145 = lean_ctor_get(x_144, 2);
lean_inc_ref(x_145);
lean_dec_ref(x_144);
lean_inc_ref(x_4);
x_146 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___boxed), 12, 5);
lean_closure_set(x_146, 0, x_1);
lean_closure_set(x_146, 1, x_142);
lean_closure_set(x_146, 2, x_34);
lean_closure_set(x_146, 3, x_133);
lean_closure_set(x_146, 4, x_4);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_143);
x_147 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___redArg(x_145, x_146, x_35, x_110, x_143, x_14, x_15);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
lean_dec_ref(x_147);
x_149 = lean_st_ref_get(x_143);
lean_dec(x_143);
lean_dec(x_149);
x_17 = x_148;
goto block_25;
}
else
{
lean_dec(x_143);
if (lean_obj_tag(x_147) == 0)
{
lean_object* x_150; 
x_150 = lean_ctor_get(x_147, 0);
lean_inc(x_150);
lean_dec_ref(x_147);
x_17 = x_150;
goto block_25;
}
else
{
lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_158; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
x_151 = lean_ctor_get(x_147, 0);
x_158 = !lean_is_exclusive(x_147);
if (x_158 == 0)
{
x_152 = x_147;
x_153 = x_158;
goto block_157;
}
else
{
lean_inc(x_151);
lean_dec(x_147);
x_152 = lean_box(0);
x_153 = x_158;
goto block_157;
}
block_157:
{
lean_object* x_154; 
if (x_153 == 0)
{
x_154 = x_152;
goto block_155;
}
else
{
lean_object* x_156; 
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_151);
x_154 = x_156;
goto block_155;
}
block_155:
{
return x_154;
}
}
}
}
}
else
{
lean_object* x_159; lean_object* x_160; 
lean_dec(x_141);
lean_dec_ref(x_139);
lean_dec(x_133);
lean_dec_ref(x_110);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_159 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__6, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__6_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__6);
x_160 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_159, x_10, x_11, x_12, x_13, x_14, x_15);
return x_160;
}
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_dec(x_138);
lean_dec(x_133);
lean_dec_ref(x_110);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_161 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__7, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__7_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__7);
x_162 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_161, x_10, x_11, x_12, x_13, x_14, x_15);
return x_162;
}
}
else
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; uint8_t x_170; 
lean_dec(x_133);
lean_dec_ref(x_110);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_163 = lean_ctor_get(x_137, 0);
x_170 = !lean_is_exclusive(x_137);
if (x_170 == 0)
{
x_164 = x_137;
x_165 = x_170;
goto block_169;
}
else
{
lean_inc(x_163);
lean_dec(x_137);
x_164 = lean_box(0);
x_165 = x_170;
goto block_169;
}
block_169:
{
lean_object* x_166; 
if (x_165 == 0)
{
x_166 = x_164;
goto block_167;
}
else
{
lean_object* x_168; 
x_168 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_168, 0, x_163);
x_166 = x_168;
goto block_167;
}
block_167:
{
return x_166;
}
}
}
}
}
}
}
else
{
lean_object* x_187; 
lean_dec(x_33);
lean_del_object(x_31);
lean_dec_ref(x_30);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_187 = l_Lean_Compiler_LCNF_ToLCNF_mkUnreachable___redArg(x_27, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
return x_187;
}
block_103:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; uint8_t x_102; 
x_44 = lean_ctor_get(x_3, 0);
x_45 = lean_ctor_get(x_3, 1);
x_102 = !lean_is_exclusive(x_3);
if (x_102 == 0)
{
x_46 = x_3;
x_47 = x_102;
goto block_101;
}
else
{
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_3);
x_46 = lean_box(0);
x_47 = x_102;
goto block_101;
}
block_101:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_array_get_size(x_6);
x_49 = l_Array_toSubarray___redArg(x_6, x_34, x_48);
if (x_47 == 0)
{
lean_ctor_set(x_46, 1, x_49);
lean_ctor_set(x_46, 0, x_36);
x_50 = x_46;
goto block_99;
}
else
{
lean_object* x_100; 
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_36);
lean_ctor_set(x_100, 1, x_49);
x_50 = x_100;
goto block_99;
}
block_99:
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_27);
lean_ctor_set(x_51, 1, x_50);
lean_inc(x_43);
lean_inc_ref(x_42);
lean_inc(x_41);
lean_inc_ref(x_40);
lean_inc(x_39);
x_52 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___redArg(x_45, x_4, x_44, x_51, x_38, x_39, x_40, x_41, x_42, x_43);
lean_dec(x_45);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_89; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
lean_dec_ref(x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_ctor_get(x_54, 0);
x_89 = !lean_is_exclusive(x_54);
if (x_89 == 0)
{
lean_object* x_90; 
x_90 = lean_ctor_get(x_54, 1);
lean_dec(x_90);
x_57 = x_54;
x_58 = x_89;
goto block_88;
}
else
{
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_box(0);
x_58 = x_89;
goto block_88;
}
block_88:
{
uint8_t x_59; lean_object* x_60; lean_object* x_61; 
x_59 = 0;
lean_inc(x_55);
x_60 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_60, 0, x_1);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_37);
lean_ctor_set(x_60, 3, x_56);
x_61 = l_Lean_Compiler_LCNF_mkAuxParam(x_59, x_55, x_35, x_40, x_41, x_42, x_43);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
lean_inc(x_62);
if (x_58 == 0)
{
lean_ctor_set_tag(x_57, 3);
lean_ctor_set(x_57, 1, x_60);
lean_ctor_set(x_57, 0, x_62);
x_63 = x_57;
goto block_78;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_79, 0, x_62);
lean_ctor_set(x_79, 1, x_60);
x_63 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_64; 
x_64 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_63, x_39);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
lean_dec_ref(x_64);
x_65 = lean_ctor_get(x_62, 0);
lean_inc(x_65);
lean_dec(x_62);
if (x_32 == 0)
{
lean_ctor_set_tag(x_31, 1);
lean_ctor_set(x_31, 0, x_65);
x_66 = x_31;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_65);
x_66 = x_69;
goto block_68;
}
block_68:
{
lean_object* x_67; 
x_67 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_66, x_4, x_5, x_38, x_39, x_40, x_41, x_42, x_43);
lean_dec_ref(x_4);
return x_67;
}
}
else
{
lean_object* x_70; lean_object* x_71; uint8_t x_72; uint8_t x_77; 
lean_dec(x_62);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_del_object(x_31);
lean_dec(x_5);
lean_dec_ref(x_4);
x_70 = lean_ctor_get(x_64, 0);
x_77 = !lean_is_exclusive(x_64);
if (x_77 == 0)
{
x_71 = x_64;
x_72 = x_77;
goto block_76;
}
else
{
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_box(0);
x_72 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_73; 
if (x_72 == 0)
{
x_73 = x_71;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_70);
x_73 = x_75;
goto block_74;
}
block_74:
{
return x_73;
}
}
}
}
}
else
{
lean_object* x_80; lean_object* x_81; uint8_t x_82; uint8_t x_87; 
lean_dec_ref(x_60);
lean_del_object(x_57);
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_del_object(x_31);
lean_dec(x_5);
lean_dec_ref(x_4);
x_80 = lean_ctor_get(x_61, 0);
x_87 = !lean_is_exclusive(x_61);
if (x_87 == 0)
{
x_81 = x_61;
x_82 = x_87;
goto block_86;
}
else
{
lean_inc(x_80);
lean_dec(x_61);
x_81 = lean_box(0);
x_82 = x_87;
goto block_86;
}
block_86:
{
lean_object* x_83; 
if (x_82 == 0)
{
x_83 = x_81;
goto block_84;
}
else
{
lean_object* x_85; 
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_80);
x_83 = x_85;
goto block_84;
}
block_84:
{
return x_83;
}
}
}
}
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; uint8_t x_98; 
lean_dec(x_43);
lean_dec_ref(x_42);
lean_dec(x_41);
lean_dec_ref(x_40);
lean_dec(x_39);
lean_dec(x_37);
lean_del_object(x_31);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_91 = lean_ctor_get(x_52, 0);
x_98 = !lean_is_exclusive(x_52);
if (x_98 == 0)
{
x_92 = x_52;
x_93 = x_98;
goto block_97;
}
else
{
lean_inc(x_91);
lean_dec(x_52);
x_92 = lean_box(0);
x_93 = x_98;
goto block_97;
}
block_97:
{
lean_object* x_94; 
if (x_93 == 0)
{
x_94 = x_92;
goto block_95;
}
else
{
lean_object* x_96; 
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_91);
x_94 = x_96;
goto block_95;
}
block_95:
{
return x_94;
}
}
}
}
}
}
}
}
else
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_29);
lean_dec(x_27);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_190 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__8, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__8_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___closed__8);
x_191 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_190, x_10, x_11, x_12, x_13, x_14, x_15);
return x_191;
}
}
else
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_199; 
lean_dec(x_27);
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_192 = lean_ctor_get(x_28, 0);
x_199 = !lean_is_exclusive(x_28);
if (x_199 == 0)
{
x_193 = x_28;
x_194 = x_199;
goto block_198;
}
else
{
lean_inc(x_192);
lean_dec(x_28);
x_193 = lean_box(0);
x_194 = x_199;
goto block_198;
}
block_198:
{
lean_object* x_195; 
if (x_194 == 0)
{
x_195 = x_193;
goto block_196;
}
else
{
lean_object* x_197; 
x_197 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_197, 0, x_192);
x_195 = x_197;
goto block_196;
}
block_196:
{
return x_195;
}
}
}
}
else
{
lean_object* x_200; lean_object* x_201; uint8_t x_202; uint8_t x_207; 
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_1);
x_200 = lean_ctor_get(x_26, 0);
x_207 = !lean_is_exclusive(x_26);
if (x_207 == 0)
{
x_201 = x_26;
x_202 = x_207;
goto block_206;
}
else
{
lean_inc(x_200);
lean_dec(x_26);
x_201 = lean_box(0);
x_202 = x_207;
goto block_206;
}
block_206:
{
lean_object* x_203; 
if (x_202 == 0)
{
x_203 = x_201;
goto block_204;
}
else
{
lean_object* x_205; 
x_205 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_205, 0, x_200);
x_203 = x_205;
goto block_204;
}
block_204:
{
return x_203;
}
}
}
block_25:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_3, 0);
lean_inc(x_18);
lean_dec_ref(x_3);
x_19 = l_Lean_instInhabitedExpr;
x_20 = lean_array_get_borrowed(x_19, x_4, x_18);
lean_dec(x_18);
lean_inc(x_20);
x_21 = l_Lean_mkAppN(x_20, x_17);
lean_dec_ref(x_17);
lean_inc(x_15);
lean_inc_ref(x_14);
lean_inc(x_13);
lean_inc_ref(x_12);
lean_inc(x_11);
x_22 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_21, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
x_24 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_23, x_4, x_5, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec_ref(x_4);
return x_24;
}
else
{
lean_dec(x_15);
lean_dec_ref(x_14);
lean_dec(x_13);
lean_dec_ref(x_12);
lean_dec(x_11);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; lean_object* x_18; 
x_17 = lean_unbox(x_10);
x_18 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_8);
lean_dec(x_7);
lean_dec_ref(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc_ref(x_13);
x_14 = lean_ctor_get(x_1, 5);
lean_inc_ref(x_14);
x_15 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_16 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_16);
x_17 = lean_mk_array(x_16, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_16, x_18);
lean_dec(x_16);
lean_inc_ref(x_2);
x_20 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_17, x_19);
lean_inc(x_11);
lean_inc_ref(x_20);
x_21 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__1___boxed), 16, 8);
lean_closure_set(x_21, 0, x_10);
lean_closure_set(x_21, 1, x_1);
lean_closure_set(x_21, 2, x_13);
lean_closure_set(x_21, 3, x_20);
lean_closure_set(x_21, 4, x_11);
lean_closure_set(x_21, 5, x_14);
lean_closure_set(x_21, 6, x_12);
lean_closure_set(x_21, 7, x_18);
x_22 = l_Lean_Expr_getAppFn(x_2);
x_23 = lean_unsigned_to_nat(0u);
lean_inc(x_11);
x_24 = l_Array_toSubarray___redArg(x_20, x_23, x_11);
x_25 = l_Subarray_copy___redArg(x_24);
x_26 = l_Lean_mkAppN(x_22, x_25);
lean_dec_ref(x_25);
x_27 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__2___boxed), 10, 3);
lean_closure_set(x_27, 0, x_23);
lean_closure_set(x_27, 1, x_26);
lean_closure_set(x_27, 2, x_21);
x_28 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_11, x_27, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
return x_28;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_3, x_13);
if (x_14 == 1)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_5);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_32; uint8_t x_33; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_3, x_16);
lean_dec(x_3);
x_32 = lean_array_fget_borrowed(x_2, x_4);
if (x_6 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
x_33 = x_6;
goto block_35;
}
else
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_36, 3);
x_38 = lean_nat_dec_lt(x_4, x_37);
x_33 = x_38;
goto block_35;
}
}
else
{
lean_object* x_39; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_39 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_32, x_6, x_7, x_8, x_9, x_10, x_11);
x_18 = x_39;
goto block_31;
}
block_31:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
x_20 = lean_nat_add(x_4, x_16);
lean_dec(x_4);
x_21 = lean_array_push(x_5, x_19);
x_3 = x_17;
x_4 = x_20;
x_5 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; uint8_t x_30; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_5);
lean_dec(x_4);
x_23 = lean_ctor_get(x_18, 0);
x_30 = !lean_is_exclusive(x_18);
if (x_30 == 0)
{
x_24 = x_18;
x_25 = x_30;
goto block_29;
}
else
{
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_box(0);
x_25 = x_30;
goto block_29;
}
block_29:
{
lean_object* x_26; 
if (x_25 == 0)
{
x_26 = x_24;
goto block_27;
}
else
{
lean_object* x_28; 
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_23);
x_26 = x_28;
goto block_27;
}
block_27:
{
return x_26;
}
}
}
}
block_35:
{
lean_object* x_34; 
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc(x_32);
x_34 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_32, x_33, x_7, x_8, x_9, x_10, x_11);
x_18 = x_34;
goto block_31;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(61u);
x_3 = lean_unsigned_to_nat(635u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_11);
x_12 = l_Lean_Compiler_CSimp_replaceConstant(x_11, x_1, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc(x_14);
x_16 = l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38(x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec_ref(x_16);
x_18 = lean_array_get_size(x_2);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_mk_empty_array_with_capacity(x_18);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_21 = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___redArg(x_17, x_2, x_18, x_19, x_20, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_32; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
lean_inc(x_14);
x_32 = l_Lean_hasNeverExtractAttribute(x_11, x_14);
if (x_32 == 0)
{
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
goto block_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_48; 
x_33 = lean_st_ref_take(x_4);
x_34 = lean_ctor_get(x_33, 0);
x_35 = lean_ctor_get(x_33, 1);
x_36 = lean_ctor_get(x_33, 2);
x_37 = lean_ctor_get(x_33, 3);
x_38 = lean_ctor_get(x_33, 4);
x_39 = lean_ctor_get(x_33, 5);
x_48 = !lean_is_exclusive(x_33);
if (x_48 == 0)
{
x_40 = x_33;
x_41 = x_48;
goto block_47;
}
else
{
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_33);
x_40 = lean_box(0);
x_41 = x_48;
goto block_47;
}
block_47:
{
uint8_t x_42; lean_object* x_43; 
x_42 = 0;
if (x_41 == 0)
{
x_43 = x_40;
goto block_45;
}
else
{
lean_object* x_46; 
x_46 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_46, 0, x_34);
lean_ctor_set(x_46, 1, x_35);
lean_ctor_set(x_46, 2, x_36);
lean_ctor_set(x_46, 3, x_37);
lean_ctor_set(x_46, 4, x_38);
lean_ctor_set(x_46, 5, x_39);
x_43 = x_46;
goto block_45;
}
block_45:
{
lean_object* x_44; 
lean_ctor_set_uint8(x_43, sizeof(void*)*6, x_42);
x_44 = lean_st_ref_set(x_4, x_43);
x_23 = x_4;
x_24 = x_5;
x_25 = x_6;
x_26 = x_7;
x_27 = x_8;
goto block_31;
}
}
}
block_31:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_28, 0, x_14);
lean_ctor_set(x_28, 1, x_15);
lean_ctor_set(x_28, 2, x_22);
x_29 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
x_30 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_28, x_29, x_23, x_24, x_25, x_26, x_27);
lean_dec(x_23);
return x_30;
}
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_56; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_49 = lean_ctor_get(x_21, 0);
x_56 = !lean_is_exclusive(x_21);
if (x_56 == 0)
{
x_50 = x_21;
x_51 = x_56;
goto block_55;
}
else
{
lean_inc(x_49);
lean_dec(x_21);
x_50 = lean_box(0);
x_51 = x_56;
goto block_55;
}
block_55:
{
lean_object* x_52; 
if (x_51 == 0)
{
x_52 = x_50;
goto block_53;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_52 = x_54;
goto block_53;
}
block_53:
{
return x_52;
}
}
}
}
else
{
lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_64; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_57 = lean_ctor_get(x_16, 0);
x_64 = !lean_is_exclusive(x_16);
if (x_64 == 0)
{
x_58 = x_16;
x_59 = x_64;
goto block_63;
}
else
{
lean_inc(x_57);
lean_dec(x_16);
x_58 = lean_box(0);
x_59 = x_64;
goto block_63;
}
block_63:
{
lean_object* x_60; 
if (x_59 == 0)
{
x_60 = x_58;
goto block_61;
}
else
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_57);
x_60 = x_62;
goto block_61;
}
block_61:
{
return x_60;
}
}
}
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_13);
lean_dec_ref(x_11);
x_65 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__1, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___closed__1);
x_66 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_65, x_3, x_4, x_5, x_6, x_7, x_8);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; uint8_t x_74; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_67 = lean_ctor_get(x_12, 0);
x_74 = !lean_is_exclusive(x_12);
if (x_74 == 0)
{
x_68 = x_12;
x_69 = x_74;
goto block_73;
}
else
{
lean_inc(x_67);
lean_dec(x_12);
x_68 = lean_box(0);
x_69 = x_74;
goto block_73;
}
block_73:
{
lean_object* x_70; 
if (x_69 == 0)
{
x_70 = x_68;
goto block_71;
}
else
{
lean_object* x_72; 
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_67);
x_70 = x_72;
goto block_71;
}
block_71:
{
return x_70;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = l_Lean_Expr_getAppFn(x_2);
x_11 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_12 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
lean_inc_ref(x_2);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_13, x_15);
x_17 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___lam__0___boxed), 9, 2);
lean_closure_set(x_17, 0, x_10);
lean_closure_set(x_17, 1, x_16);
x_18 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_2, x_1, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(45u);
x_3 = lean_unsigned_to_nat(755u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__10(size_t x_1, size_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_2, x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_3);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_array_uget_borrowed(x_3, x_2);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_14 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_13, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = 1;
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_17, x_2, x_15);
x_2 = x_19;
x_3 = x_20;
goto _start;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_29; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_3);
x_22 = lean_ctor_get(x_14, 0);
x_29 = !lean_is_exclusive(x_14);
if (x_29 == 0)
{
x_23 = x_14;
x_24 = x_29;
goto block_28;
}
else
{
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_box(0);
x_24 = x_29;
goto block_28;
}
block_28:
{
lean_object* x_25; 
if (x_24 == 0)
{
x_25 = x_23;
goto block_26;
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_22);
x_25 = x_27;
goto block_26;
}
block_26:
{
return x_25;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(59u);
x_3 = lean_unsigned_to_nat(507u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_st_ref_get(x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_11);
x_12 = l_Lean_Compiler_CSimp_replaceConstant(x_11, x_1, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec_ref(x_13);
x_16 = lean_array_size(x_2);
x_17 = 0;
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
x_18 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__10(x_16, x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec_ref(x_18);
lean_inc(x_14);
x_29 = l_Lean_hasNeverExtractAttribute(x_11, x_14);
if (x_29 == 0)
{
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
goto block_28;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; uint8_t x_45; 
x_30 = lean_st_ref_take(x_4);
x_31 = lean_ctor_get(x_30, 0);
x_32 = lean_ctor_get(x_30, 1);
x_33 = lean_ctor_get(x_30, 2);
x_34 = lean_ctor_get(x_30, 3);
x_35 = lean_ctor_get(x_30, 4);
x_36 = lean_ctor_get(x_30, 5);
x_45 = !lean_is_exclusive(x_30);
if (x_45 == 0)
{
x_37 = x_30;
x_38 = x_45;
goto block_44;
}
else
{
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_30);
x_37 = lean_box(0);
x_38 = x_45;
goto block_44;
}
block_44:
{
uint8_t x_39; lean_object* x_40; 
x_39 = 0;
if (x_38 == 0)
{
x_40 = x_37;
goto block_42;
}
else
{
lean_object* x_43; 
x_43 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_43, 0, x_31);
lean_ctor_set(x_43, 1, x_32);
lean_ctor_set(x_43, 2, x_33);
lean_ctor_set(x_43, 3, x_34);
lean_ctor_set(x_43, 4, x_35);
lean_ctor_set(x_43, 5, x_36);
x_40 = x_43;
goto block_42;
}
block_42:
{
lean_object* x_41; 
lean_ctor_set_uint8(x_40, sizeof(void*)*6, x_39);
x_41 = lean_st_ref_set(x_4, x_40);
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
goto block_28;
}
}
}
block_28:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_25, 0, x_14);
lean_ctor_set(x_25, 1, x_15);
lean_ctor_set(x_25, 2, x_19);
x_26 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
x_27 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_25, x_26, x_20, x_21, x_22, x_23, x_24);
lean_dec(x_20);
return x_27;
}
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_53; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_46 = lean_ctor_get(x_18, 0);
x_53 = !lean_is_exclusive(x_18);
if (x_53 == 0)
{
x_47 = x_18;
x_48 = x_53;
goto block_52;
}
else
{
lean_inc(x_46);
lean_dec(x_18);
x_47 = lean_box(0);
x_48 = x_53;
goto block_52;
}
block_52:
{
lean_object* x_49; 
if (x_48 == 0)
{
x_49 = x_47;
goto block_50;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_46);
x_49 = x_51;
goto block_50;
}
block_50:
{
return x_49;
}
}
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_13);
lean_dec_ref(x_11);
lean_dec_ref(x_2);
x_54 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___closed__1);
x_55 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_54, x_3, x_4, x_5, x_6, x_7, x_8);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_dec_ref(x_11);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_56 = lean_ctor_get(x_12, 0);
x_63 = !lean_is_exclusive(x_12);
if (x_63 == 0)
{
x_57 = x_12;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_12);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = l_Lean_Name_getPrefix(x_10);
x_13 = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_14) == 4)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec_ref(x_14);
lean_inc_ref(x_7);
x_17 = l_Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17(x_15, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = l_Lean_Core_instantiateValueLevelParams(x_18, x_16, x_7, x_8);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec_ref(x_19);
x_21 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_22 = l_Lean_Expr_getAppNumArgs(x_2);
lean_inc(x_22);
x_23 = lean_mk_array(x_22, x_21);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_22, x_24);
lean_dec(x_22);
x_26 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_23, x_25);
x_27 = l_Lean_Expr_beta(x_20, x_26);
x_28 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_27, x_3, x_4, x_5, x_6, x_7, x_8);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_29 = lean_ctor_get(x_19, 0);
x_36 = !lean_is_exclusive(x_19);
if (x_36 == 0)
{
x_30 = x_19;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_44; 
lean_dec(x_16);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_37 = lean_ctor_get(x_17, 0);
x_44 = !lean_is_exclusive(x_17);
if (x_44 == 0)
{
x_38 = x_17;
x_39 = x_44;
goto block_43;
}
else
{
lean_inc(x_37);
lean_dec(x_17);
x_38 = lean_box(0);
x_39 = x_44;
goto block_43;
}
block_43:
{
lean_object* x_40; 
if (x_39 == 0)
{
x_40 = x_38;
goto block_41;
}
else
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_40 = x_42;
goto block_41;
}
block_41:
{
return x_40;
}
}
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec_ref(x_14);
lean_dec_ref(x_2);
x_45 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___closed__1);
x_46 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_45, x_3, x_4, x_5, x_6, x_7, x_8);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = l_Lean_Expr_getAppNumArgs(x_2);
x_48 = lean_unsigned_to_nat(1u);
x_49 = lean_nat_add(x_11, x_48);
x_50 = lean_nat_dec_lt(x_47, x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_49);
x_51 = l_Lean_Expr_getAppFn(x_2);
x_52 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
lean_inc(x_47);
x_53 = lean_mk_array(x_47, x_52);
x_54 = lean_nat_sub(x_47, x_48);
lean_dec(x_47);
x_55 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_2, x_53, x_54);
x_56 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_51, x_55, x_3, x_4, x_5, x_6, x_7, x_8);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_nat_sub(x_49, x_47);
lean_dec(x_47);
lean_dec(x_49);
lean_inc(x_8);
lean_inc_ref(x_7);
x_58 = l_Lean_Compiler_LCNF_ToLCNF_etaExpandN___redArg(x_2, x_57, x_4, x_7, x_8);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
lean_dec_ref(x_58);
x_60 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_59, x_3, x_4, x_5, x_6, x_7, x_8);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_68; 
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
x_61 = lean_ctor_get(x_58, 0);
x_68 = !lean_is_exclusive(x_58);
if (x_68 == 0)
{
x_62 = x_58;
x_63 = x_68;
goto block_67;
}
else
{
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_box(0);
x_63 = x_68;
goto block_67;
}
block_67:
{
lean_object* x_64; 
if (x_63 == 0)
{
x_64 = x_62;
goto block_65;
}
else
{
lean_object* x_66; 
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_61);
x_64 = x_66;
goto block_65;
}
block_65:
{
return x_64;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_array_set(x_2, x_3, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_1 = x_11;
x_2 = x_13;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
x_17 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc_ref(x_9);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_expandNoConfusionMajor___redArg(x_1, x_2, x_6, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_3);
x_23 = lean_nat_dec_le(x_4, x_21);
if (x_23 == 0)
{
x_14 = x_4;
x_15 = x_22;
goto block_20;
}
else
{
lean_dec(x_4);
x_14 = x_21;
x_15 = x_22;
goto block_20;
}
block_20:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = l_Array_toSubarray___redArg(x_3, x_14, x_15);
x_17 = l_Subarray_copy___redArg(x_16);
x_18 = l_Lean_mkAppN(x_13, x_17);
lean_dec_ref(x_17);
x_19 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_18, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_31; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec_ref(x_3);
x_24 = lean_ctor_get(x_12, 0);
x_31 = !lean_is_exclusive(x_12);
if (x_31 == 0)
{
x_25 = x_12;
x_26 = x_31;
goto block_30;
}
else
{
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_box(0);
x_26 = x_31;
goto block_30;
}
block_30:
{
lean_object* x_27; 
if (x_26 == 0)
{
x_27 = x_25;
goto block_28;
}
else
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_27 = x_29;
goto block_28;
}
block_28:
{
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_nat_add(x_1, x_2);
x_15 = lean_array_get(x_3, x_4, x_1);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__0___boxed), 11, 4);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_6);
lean_closure_set(x_16, 2, x_4);
lean_closure_set(x_16, 3, x_14);
x_17 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_5, x_14, x_16, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_14);
return x_17;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
x_15 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(701u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_9) == 4)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_st_ref_get(x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = l_Lean_instInhabitedExpr;
lean_inc(x_10);
x_14 = l_Lean_getNoConfusionInfo(x_12, x_10);
x_15 = l_Lean_NoConfusionInfo_arity(x_14);
x_16 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_17 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_17);
x_18 = lean_mk_array(x_17, x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_sub(x_17, x_19);
lean_dec(x_17);
lean_inc_ref(x_1);
x_21 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_18, x_20);
lean_inc_ref(x_1);
lean_inc_ref(x_21);
lean_inc(x_15);
x_22 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__1___boxed), 13, 5);
lean_closure_set(x_22, 0, x_15);
lean_closure_set(x_22, 1, x_19);
lean_closure_set(x_22, 2, x_13);
lean_closure_set(x_22, 3, x_21);
lean_closure_set(x_22, 4, x_1);
lean_inc_ref(x_1);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___lam__3___boxed), 13, 6);
lean_closure_set(x_23, 0, x_14);
lean_closure_set(x_23, 1, x_10);
lean_closure_set(x_23, 2, x_1);
lean_closure_set(x_23, 3, x_22);
lean_closure_set(x_23, 4, x_13);
lean_closure_set(x_23, 5, x_21);
x_24 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_15, x_23, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_9);
lean_dec_ref(x_1);
x_25 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___closed__1);
x_26 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_25, x_2, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__0));
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_11, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___closed__0));
lean_inc_ref(x_1);
x_10 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___lam__1___boxed), 9, 2);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
x_11 = lean_unsigned_to_nat(2u);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_11, x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec_ref(x_11);
x_13 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; lean_object* x_28; uint8_t x_29; 
x_9 = lean_unsigned_to_nat(7u);
x_10 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
lean_inc_ref(x_1);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_12, x_14);
x_28 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__1));
x_29 = l_Lean_Expr_isAppOf(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__2));
x_31 = l_Lean_Expr_isAppOf(x_1, x_30);
x_20 = x_31;
goto block_27;
}
else
{
x_20 = x_29;
goto block_27;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed), 10, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_9);
x_18 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_9, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
block_27:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_unsigned_to_nat(6u);
x_23 = lean_array_get(x_21, x_15, x_22);
x_16 = x_23;
goto block_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_instInhabitedExpr;
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_array_get(x_24, x_15, x_25);
x_16 = x_26;
goto block_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_20; lean_object* x_28; uint8_t x_29; 
x_9 = lean_unsigned_to_nat(6u);
x_10 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_11 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_11);
x_12 = lean_mk_array(x_11, x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_sub(x_11, x_13);
lean_dec(x_11);
lean_inc_ref(x_1);
x_15 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_12, x_14);
x_28 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__1));
x_29 = l_Lean_Expr_isAppOf(x_1, x_28);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
x_30 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2));
x_31 = l_Lean_Expr_isAppOf(x_1, x_30);
x_20 = x_31;
goto block_27;
}
else
{
x_20 = x_29;
goto block_27;
}
block_19:
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___lam__0___boxed), 10, 3);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_15);
lean_closure_set(x_17, 2, x_9);
x_18 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_9, x_17, x_2, x_3, x_4, x_5, x_6, x_7);
return x_18;
}
block_27:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_unsigned_to_nat(5u);
x_23 = lean_array_get(x_21, x_15, x_22);
x_16 = x_23;
goto block_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_instInhabitedExpr;
x_25 = lean_unsigned_to_nat(3u);
x_26 = lean_array_get(x_24, x_15, x_25);
x_16 = x_26;
goto block_19;
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(42u);
x_3 = lean_unsigned_to_nat(655u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(19u);
x_3 = lean_unsigned_to_nat(659u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
x_14 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_1, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec_ref(x_14);
lean_inc_ref(x_2);
x_16 = lean_array_get_borrowed(x_2, x_3, x_4);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_17 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_16, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec_ref(x_17);
x_19 = lean_unsigned_to_nat(3u);
lean_inc_ref(x_2);
x_20 = lean_array_get_borrowed(x_2, x_3, x_19);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_20);
x_21 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_20, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = lean_unsigned_to_nat(5u);
x_24 = lean_array_get_borrowed(x_2, x_3, x_23);
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc(x_24);
x_25 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_24, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_36 = l_Lean_Expr_getAppFn(x_5);
if (lean_obj_tag(x_36) == 4)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec_ref(x_36);
if (lean_obj_tag(x_37) == 1)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 1)
{
lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_96; 
x_39 = lean_ctor_get(x_38, 1);
x_96 = !lean_is_exclusive(x_38);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_38, 0);
lean_dec(x_97);
x_40 = x_38;
x_41 = x_96;
goto block_95;
}
else
{
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_box(0);
x_41 = x_96;
goto block_95;
}
block_95:
{
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; uint8_t x_93; 
x_42 = lean_ctor_get(x_37, 0);
x_93 = !lean_is_exclusive(x_37);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_37, 1);
lean_dec(x_94);
x_43 = x_37;
x_44 = x_93;
goto block_92;
}
else
{
lean_inc(x_42);
lean_dec(x_37);
x_43 = lean_box(0);
x_44 = x_93;
goto block_92;
}
block_92:
{
lean_object* x_45; lean_object* x_46; 
x_45 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__3));
if (x_41 == 0)
{
lean_ctor_set(x_40, 0, x_42);
x_46 = x_40;
goto block_90;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_42);
lean_ctor_set(x_91, 1, x_39);
x_46 = x_91;
goto block_90;
}
block_90:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_47 = lean_mk_empty_array_with_capacity(x_19);
x_48 = lean_array_push(x_47, x_15);
x_49 = lean_array_push(x_48, x_18);
x_50 = lean_array_push(x_49, x_26);
x_51 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_46);
lean_ctor_set(x_51, 2, x_50);
x_52 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_53 = l_Lean_Compiler_LCNF_ToLCNF_mkAuxLetDecl___redArg(x_51, x_52, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
switch (lean_obj_tag(x_22)) {
case 0:
{
lean_object* x_54; uint8_t x_55; uint8_t x_61; 
lean_del_object(x_43);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_61 = !lean_is_exclusive(x_53);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_53, 0);
lean_dec(x_62);
x_54 = x_53;
x_55 = x_61;
goto block_60;
}
else
{
lean_dec(x_53);
x_54 = lean_box(0);
x_55 = x_61;
goto block_60;
}
block_60:
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_box(0);
if (x_55 == 0)
{
lean_ctor_set(x_54, 0, x_56);
x_57 = x_54;
goto block_58;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_56);
x_57 = x_59;
goto block_58;
}
block_58:
{
return x_57;
}
}
}
case 1:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_79; 
x_63 = lean_ctor_get(x_53, 0);
lean_inc(x_63);
lean_dec_ref(x_53);
x_64 = lean_ctor_get(x_22, 0);
x_79 = !lean_is_exclusive(x_22);
if (x_79 == 0)
{
x_65 = x_22;
x_66 = x_79;
goto block_78;
}
else
{
lean_inc(x_64);
lean_dec(x_22);
x_65 = lean_box(0);
x_66 = x_79;
goto block_78;
}
block_78:
{
lean_object* x_67; 
if (x_66 == 0)
{
lean_ctor_set(x_65, 0, x_63);
x_67 = x_65;
goto block_76;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_63);
x_67 = x_77;
goto block_76;
}
block_76:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_mk_empty_array_with_capacity(x_4);
x_69 = lean_array_push(x_68, x_67);
if (x_44 == 0)
{
lean_ctor_set_tag(x_43, 4);
lean_ctor_set(x_43, 1, x_69);
lean_ctor_set(x_43, 0, x_64);
x_70 = x_43;
goto block_74;
}
else
{
lean_object* x_75; 
x_75 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_75, 0, x_64);
lean_ctor_set(x_75, 1, x_69);
x_70 = x_75;
goto block_74;
}
block_74:
{
lean_object* x_71; 
lean_inc(x_12);
lean_inc_ref(x_11);
lean_inc(x_10);
lean_inc_ref(x_9);
x_71 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_70, x_52, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec_ref(x_71);
x_73 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_72, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_73;
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_71;
}
}
}
}
}
default: 
{
lean_object* x_80; lean_object* x_81; 
lean_dec_ref(x_22);
lean_dec_ref(x_53);
lean_del_object(x_43);
lean_dec(x_6);
x_80 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__4);
x_81 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_80, x_7, x_8, x_9, x_10, x_11, x_12);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; uint8_t x_89; 
lean_del_object(x_43);
lean_dec(x_22);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_82 = lean_ctor_get(x_53, 0);
x_89 = !lean_is_exclusive(x_53);
if (x_89 == 0)
{
x_83 = x_53;
x_84 = x_89;
goto block_88;
}
else
{
lean_inc(x_82);
lean_dec(x_53);
x_83 = lean_box(0);
x_84 = x_89;
goto block_88;
}
block_88:
{
lean_object* x_85; 
if (x_84 == 0)
{
x_85 = x_83;
goto block_86;
}
else
{
lean_object* x_87; 
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_82);
x_85 = x_87;
goto block_86;
}
block_86:
{
return x_85;
}
}
}
}
}
}
else
{
lean_del_object(x_40);
lean_dec(x_39);
lean_dec_ref(x_37);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
goto block_35;
}
}
}
else
{
lean_dec_ref(x_37);
lean_dec(x_38);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
goto block_35;
}
}
else
{
lean_dec(x_37);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
goto block_35;
}
}
else
{
lean_dec_ref(x_36);
lean_dec(x_26);
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_6);
x_27 = x_7;
x_28 = x_8;
x_29 = x_9;
x_30 = x_10;
x_31 = x_11;
x_32 = x_12;
goto block_35;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___closed__1);
x_34 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_33, x_27, x_28, x_29, x_30, x_31, x_32);
return x_34;
}
}
else
{
lean_dec(x_22);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_25;
}
}
else
{
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_21;
}
}
else
{
lean_dec(x_15);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_17;
}
}
else
{
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
x_15 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_unsigned_to_nat(6u);
x_11 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
lean_inc_ref(x_1);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_13, x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get(x_9, x_16, x_17);
lean_inc_ref(x_1);
x_19 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___lam__0___boxed), 13, 6);
lean_closure_set(x_19, 0, x_18);
lean_closure_set(x_19, 1, x_9);
lean_closure_set(x_19, 2, x_16);
lean_closure_set(x_19, 3, x_14);
lean_closure_set(x_19, 4, x_1);
lean_closure_set(x_19, 5, x_10);
x_20 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_10, x_19, x_2, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_12);
lean_dec_ref(x_1);
x_13 = lean_array_set(x_2, x_3, x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_1 = x_11;
x_2 = x_13;
x_3 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_3);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_17 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_42; 
x_18 = lean_ctor_get(x_17, 0);
x_42 = !lean_is_exclusive(x_17);
if (x_42 == 0)
{
x_19 = x_17;
x_20 = x_42;
goto block_41;
}
else
{
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_box(0);
x_20 = x_42;
goto block_41;
}
block_41:
{
if (lean_obj_tag(x_18) == 1)
{
lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
lean_del_object(x_19);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec_ref(x_18);
x_22 = lean_array_size(x_2);
x_23 = 0;
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_24 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__10(x_22, x_23, x_2, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec_ref(x_24);
x_26 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_25);
x_27 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
x_28 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_26, x_27, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; uint8_t x_36; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_29 = lean_ctor_get(x_24, 0);
x_36 = !lean_is_exclusive(x_24);
if (x_36 == 0)
{
x_30 = x_24;
x_31 = x_36;
goto block_35;
}
else
{
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = x_36;
goto block_35;
}
block_35:
{
lean_object* x_32; 
if (x_31 == 0)
{
x_32 = x_30;
goto block_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_29);
x_32 = x_34;
goto block_33;
}
block_33:
{
return x_32;
}
}
}
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
x_37 = lean_box(0);
if (x_20 == 0)
{
lean_ctor_set(x_19, 0, x_37);
x_38 = x_19;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_2);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = l_Lean_Expr_getAppFn(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
x_12 = l_Lean_Compiler_CSimp_replaceConstant(x_10, x_11, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
if (lean_obj_tag(x_13) == 4)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_14);
x_15 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_checkComputable(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_dec_ref(x_15);
x_19 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__0));
x_20 = lean_name_eq(x_14, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__1));
x_22 = lean_name_eq(x_14, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___closed__1));
x_24 = lean_name_eq(x_14, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__3));
x_26 = lean_name_eq(x_14, x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand___closed__2));
x_28 = lean_name_eq(x_14, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__1));
x_30 = lean_name_eq(x_14, x_29);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___closed__2));
x_32 = lean_name_eq(x_14, x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__5));
x_34 = lean_name_eq(x_14, x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__7));
x_36 = lean_name_eq(x_14, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__9));
x_38 = lean_name_eq(x_14, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint8_t x_40; 
x_39 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__11));
x_40 = lean_name_eq(x_14, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___closed__13));
x_42 = lean_name_eq(x_14, x_41);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_14);
x_43 = l_getCasesInfo_x3f(x_14, x_6, x_7);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
lean_dec_ref(x_43);
if (lean_obj_tag(x_44) == 1)
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_14);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec_ref(x_44);
x_46 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(x_45, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_46;
}
else
{
lean_object* x_47; 
lean_dec(x_44);
lean_inc_ref(x_6);
lean_inc(x_14);
x_47 = l_Lean_Compiler_LCNF_getCtorArity_x3f(x_14, x_6, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec_ref(x_47);
if (lean_obj_tag(x_48) == 1)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_14);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
lean_dec_ref(x_48);
x_50 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_49, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_48);
x_51 = lean_st_ref_get(x_7);
x_52 = lean_ctor_get(x_51, 0);
lean_inc_ref(x_52);
lean_dec(x_51);
lean_inc(x_14);
x_53 = l_Lean_isNoConfusion(x_52, x_14);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___redArg(x_14, x_7);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
lean_dec_ref(x_54);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_57 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_56, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_dec(x_55);
x_58 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_59 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_59);
x_60 = lean_mk_array(x_59, x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_59, x_61);
lean_dec(x_59);
x_63 = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__12(x_1, x_60, x_62, x_2, x_3, x_4, x_5, x_6, x_7);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; uint8_t x_71; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_64 = lean_ctor_get(x_54, 0);
x_71 = !lean_is_exclusive(x_54);
if (x_71 == 0)
{
x_65 = x_54;
x_66 = x_71;
goto block_70;
}
else
{
lean_inc(x_64);
lean_dec(x_54);
x_65 = lean_box(0);
x_66 = x_71;
goto block_70;
}
block_70:
{
lean_object* x_67; 
if (x_66 == 0)
{
x_67 = x_65;
goto block_68;
}
else
{
lean_object* x_69; 
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_64);
x_67 = x_69;
goto block_68;
}
block_68:
{
return x_67;
}
}
}
}
else
{
lean_object* x_72; 
lean_dec(x_14);
x_72 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; uint8_t x_80; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_73 = lean_ctor_get(x_47, 0);
x_80 = !lean_is_exclusive(x_47);
if (x_80 == 0)
{
x_74 = x_47;
x_75 = x_80;
goto block_79;
}
else
{
lean_inc(x_73);
lean_dec(x_47);
x_74 = lean_box(0);
x_75 = x_80;
goto block_79;
}
block_79:
{
lean_object* x_76; 
if (x_75 == 0)
{
x_76 = x_74;
goto block_77;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_73);
x_76 = x_78;
goto block_77;
}
block_77:
{
return x_76;
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_43, 0);
x_88 = !lean_is_exclusive(x_43);
if (x_88 == 0)
{
x_82 = x_43;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_43);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
else
{
lean_object* x_89; 
lean_dec(x_14);
x_89 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec(x_14);
x_90 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_90;
}
}
else
{
lean_object* x_91; 
lean_dec(x_14);
x_91 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_91;
}
}
else
{
lean_dec(x_14);
goto block_18;
}
}
else
{
lean_dec(x_14);
goto block_18;
}
}
else
{
lean_object* x_92; 
lean_dec(x_14);
x_92 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_dec(x_14);
x_93 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_93;
}
}
else
{
lean_object* x_94; 
lean_dec(x_14);
x_94 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_94;
}
}
else
{
lean_object* x_95; 
lean_dec(x_14);
x_95 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_95;
}
}
else
{
lean_object* x_96; 
lean_dec(x_14);
x_96 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_14);
x_97 = lean_unsigned_to_nat(3u);
x_98 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_97, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_98;
}
}
else
{
lean_object* x_99; 
lean_dec(x_14);
x_99 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_99;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(3u);
x_17 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_16, x_2, x_3, x_4, x_5, x_6, x_7);
return x_17;
}
}
else
{
lean_object* x_100; lean_object* x_101; uint8_t x_102; uint8_t x_107; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_100 = lean_ctor_get(x_15, 0);
x_107 = !lean_is_exclusive(x_15);
if (x_107 == 0)
{
x_101 = x_15;
x_102 = x_107;
goto block_106;
}
else
{
lean_inc(x_100);
lean_dec(x_15);
x_101 = lean_box(0);
x_102 = x_107;
goto block_106;
}
block_106:
{
lean_object* x_103; 
if (x_102 == 0)
{
x_103 = x_101;
goto block_104;
}
else
{
lean_object* x_105; 
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_100);
x_103 = x_105;
goto block_104;
}
block_104:
{
return x_103;
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_13);
x_108 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___closed__0);
x_109 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_109);
x_110 = lean_mk_array(x_109, x_108);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_nat_sub(x_109, x_111);
lean_dec(x_109);
x_113 = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__13(x_1, x_110, x_112, x_2, x_3, x_4, x_5, x_6, x_7);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; uint8_t x_121; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_114 = lean_ctor_get(x_12, 0);
x_121 = !lean_is_exclusive(x_12);
if (x_121 == 0)
{
x_115 = x_12;
x_116 = x_121;
goto block_120;
}
else
{
lean_inc(x_114);
lean_dec(x_12);
x_115 = lean_box(0);
x_116 = x_121;
goto block_120;
}
block_120:
{
lean_object* x_117; 
if (x_116 == 0)
{
x_117 = x_115;
goto block_118;
}
else
{
lean_object* x_119; 
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_114);
x_117 = x_119;
goto block_118;
}
block_118:
{
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
x_9 = l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_13 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_12, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec_ref(x_13);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg(x_14, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___closed__1));
x_18 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_11, x_16, x_17, x_4, x_5, x_6, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
x_19 = lean_ctor_get(x_15, 0);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
x_20 = x_15;
x_21 = x_26;
goto block_25;
}
else
{
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_box(0);
x_21 = x_26;
goto block_25;
}
block_25:
{
lean_object* x_22; 
if (x_21 == 0)
{
x_22 = x_20;
goto block_23;
}
else
{
lean_object* x_24; 
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_22 = x_24;
goto block_23;
}
block_23:
{
return x_22;
}
}
}
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_34; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_27 = lean_ctor_get(x_13, 0);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
x_28 = x_13;
x_29 = x_34;
goto block_33;
}
else
{
lean_inc(x_27);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = x_34;
goto block_33;
}
block_33:
{
lean_object* x_30; 
if (x_29 == 0)
{
x_30 = x_28;
goto block_31;
}
else
{
lean_object* x_32; 
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_27);
x_30 = x_32;
goto block_31;
}
block_31:
{
return x_30;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; uint8_t x_42; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_35 = lean_ctor_get(x_9, 0);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
x_36 = x_9;
x_37 = x_42;
goto block_41;
}
else
{
lean_inc(x_35);
lean_dec(x_9);
x_36 = lean_box(0);
x_37 = x_42;
goto block_41;
}
block_41:
{
lean_object* x_38; 
if (x_37 == 0)
{
x_38 = x_36;
goto block_39;
}
else
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_38 = x_40;
goto block_39;
}
block_39:
{
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_43; uint8_t x_44; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
lean_inc_ref(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___lam__0___boxed), 8, 1);
lean_closure_set(x_11, 0, x_1);
x_43 = l_Lean_Compiler_LCNF_ToLCNF_etaReduceImplicit(x_1);
x_44 = l_Lean_Expr_isLambda(x_43);
if (x_44 == 0)
{
uint8_t x_45; 
x_45 = l_Lean_Compiler_LCNF_ToLCNF_mustEtaExpand(x_10, x_43);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec_ref(x_11);
x_46 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_43, x_2, x_3, x_4, x_5, x_6, x_7);
return x_46;
}
else
{
lean_dec_ref(x_43);
goto block_42;
}
}
else
{
lean_dec_ref(x_43);
lean_dec_ref(x_10);
goto block_42;
}
block_42:
{
lean_object* x_12; 
lean_inc(x_3);
x_12 = l_Lean_Compiler_LCNF_ToLCNF_withNewScope___redArg(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec_ref(x_12);
lean_inc(x_13);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = l_Lean_Compiler_LCNF_ToLCNF_pushElement___redArg(x_14, x_3);
lean_dec(x_3);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_24; 
x_24 = !lean_is_exclusive(x_15);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_15, 0);
lean_dec(x_25);
x_16 = x_15;
x_17 = x_24;
goto block_23;
}
else
{
lean_dec(x_15);
x_16 = lean_box(0);
x_17 = x_24;
goto block_23;
}
block_23:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_13, 0);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
if (x_17 == 0)
{
lean_ctor_set(x_16, 0, x_19);
x_20 = x_16;
goto block_21;
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
x_20 = x_22;
goto block_21;
}
block_21:
{
return x_20;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_33; 
lean_dec(x_13);
x_26 = lean_ctor_get(x_15, 0);
x_33 = !lean_is_exclusive(x_15);
if (x_33 == 0)
{
x_27 = x_15;
x_28 = x_33;
goto block_32;
}
else
{
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_box(0);
x_28 = x_33;
goto block_32;
}
block_32:
{
lean_object* x_29; 
if (x_28 == 0)
{
x_29 = x_27;
goto block_30;
}
else
{
lean_object* x_31; 
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_26);
x_29 = x_31;
goto block_30;
}
block_30:
{
return x_29;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; uint8_t x_41; 
lean_dec(x_3);
x_34 = lean_ctor_get(x_12, 0);
x_41 = !lean_is_exclusive(x_12);
if (x_41 == 0)
{
x_35 = x_12;
x_36 = x_41;
goto block_40;
}
else
{
lean_inc(x_34);
lean_dec(x_12);
x_35 = lean_box(0);
x_36 = x_41;
goto block_40;
}
block_40:
{
lean_object* x_37; 
if (x_36 == 0)
{
x_37 = x_35;
goto block_38;
}
else
{
lean_object* x_39; 
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_34);
x_37 = x_39;
goto block_38;
}
block_38:
{
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 8)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_33; lean_object* x_72; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc_ref(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc_ref(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc_ref(x_13);
lean_dec_ref(x_1);
x_14 = lean_st_ref_get(x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_box(1);
x_17 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_18 = 0;
x_19 = lean_unsigned_to_nat(0u);
x_20 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_21 = lean_box(0);
x_22 = 1;
x_23 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_19);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*7, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 1, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 2, x_18);
lean_ctor_set_uint8(x_23, sizeof(void*)*7 + 3, x_22);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_mk_empty_array_with_capacity(x_24);
lean_dec_ref(x_25);
x_26 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_27 = lean_st_mk_ref(x_26);
x_28 = lean_expr_instantiate_rev(x_11, x_2);
lean_dec_ref(x_11);
x_29 = lean_expr_instantiate_rev(x_12, x_2);
lean_dec_ref(x_12);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_27);
lean_inc_ref(x_28);
x_72 = l_Lean_Meta_isProp(x_28, x_23, x_27, x_7, x_8);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec_ref(x_72);
x_74 = lean_st_ref_get(x_27);
lean_dec(x_27);
lean_dec(x_74);
x_75 = lean_unbox(x_73);
lean_dec(x_73);
x_33 = x_75;
goto block_71;
}
else
{
lean_dec(x_27);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_76; uint8_t x_77; 
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
lean_dec_ref(x_72);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
x_33 = x_77;
goto block_71;
}
else
{
lean_object* x_78; lean_object* x_79; uint8_t x_80; uint8_t x_85; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_78 = lean_ctor_get(x_72, 0);
x_85 = !lean_is_exclusive(x_72);
if (x_85 == 0)
{
x_79 = x_72;
x_80 = x_85;
goto block_84;
}
else
{
lean_inc(x_78);
lean_dec(x_72);
x_79 = lean_box(0);
x_80 = x_85;
goto block_84;
}
block_84:
{
lean_object* x_81; 
if (x_80 == 0)
{
x_81 = x_79;
goto block_82;
}
else
{
lean_object* x_83; 
x_83 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_83, 0, x_78);
x_81 = x_83;
goto block_82;
}
block_82:
{
return x_81;
}
}
}
}
block_32:
{
lean_object* x_30; 
x_30 = lean_array_push(x_2, x_29);
x_1 = x_13;
x_2 = x_30;
goto _start;
}
block_71:
{
if (x_33 == 0)
{
lean_object* x_34; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_28);
x_34 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_28, x_4, x_7, x_8);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
lean_dec_ref(x_34);
x_36 = lean_unbox(x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc_ref(x_28);
x_37 = l_Lean_Compiler_LCNF_ToLCNF_toLCNFType___redArg(x_28, x_4, x_7, x_8);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec_ref(x_37);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_4);
lean_inc_ref(x_29);
x_39 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_29, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Compiler_LCNF_ToLCNF_mkLetDecl___redArg(x_10, x_28, x_29, x_38, x_40, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_40);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec_ref(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
x_44 = l_Lean_Expr_fvar___override(x_43);
x_45 = lean_array_push(x_2, x_44);
x_1 = x_13;
x_2 = x_45;
goto _start;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_54; 
lean_dec_ref(x_13);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_47 = lean_ctor_get(x_41, 0);
x_54 = !lean_is_exclusive(x_41);
if (x_54 == 0)
{
x_48 = x_41;
x_49 = x_54;
goto block_53;
}
else
{
lean_inc(x_47);
lean_dec(x_41);
x_48 = lean_box(0);
x_49 = x_54;
goto block_53;
}
block_53:
{
lean_object* x_50; 
if (x_49 == 0)
{
x_50 = x_48;
goto block_51;
}
else
{
lean_object* x_52; 
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_50 = x_52;
goto block_51;
}
block_51:
{
return x_50;
}
}
}
}
else
{
lean_dec(x_38);
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
return x_39;
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_62; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_55 = lean_ctor_get(x_37, 0);
x_62 = !lean_is_exclusive(x_37);
if (x_62 == 0)
{
x_56 = x_37;
x_57 = x_62;
goto block_61;
}
else
{
lean_inc(x_55);
lean_dec(x_37);
x_56 = lean_box(0);
x_57 = x_62;
goto block_61;
}
block_61:
{
lean_object* x_58; 
if (x_57 == 0)
{
x_58 = x_56;
goto block_59;
}
else
{
lean_object* x_60; 
x_60 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_60, 0, x_55);
x_58 = x_60;
goto block_59;
}
block_59:
{
return x_58;
}
}
}
}
else
{
lean_dec_ref(x_28);
lean_dec(x_10);
goto block_32;
}
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; uint8_t x_70; 
lean_dec_ref(x_29);
lean_dec_ref(x_28);
lean_dec_ref(x_13);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_2);
x_63 = lean_ctor_get(x_34, 0);
x_70 = !lean_is_exclusive(x_34);
if (x_70 == 0)
{
x_64 = x_34;
x_65 = x_70;
goto block_69;
}
else
{
lean_inc(x_63);
lean_dec(x_34);
x_64 = lean_box(0);
x_65 = x_70;
goto block_69;
}
block_69:
{
lean_object* x_66; 
if (x_65 == 0)
{
x_66 = x_64;
goto block_67;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_63);
x_66 = x_68;
goto block_67;
}
block_67:
{
return x_66;
}
}
}
}
else
{
lean_dec_ref(x_28);
lean_dec(x_10);
goto block_32;
}
}
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_expr_instantiate_rev(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_87 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_86, x_3, x_4, x_5, x_6, x_7, x_8);
return x_87;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_11; 
x_11 = l_Lean_Compiler_LCNF_isRuntimeBuiltinType(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_25; 
x_13 = lean_ctor_get(x_12, 0);
x_25 = !lean_is_exclusive(x_12);
if (x_25 == 0)
{
x_14 = x_12;
x_15 = x_25;
goto block_24;
}
else
{
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = x_25;
goto block_24;
}
block_24:
{
if (lean_obj_tag(x_13) == 1)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_del_object(x_14);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec_ref(x_13);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set(x_17, 2, x_16);
x_18 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_bindCases_go___closed__8));
x_19 = l_Lean_Compiler_LCNF_ToLCNF_letValueToArg___redArg(x_17, x_18, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_13);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_20 = lean_box(0);
if (x_15 == 0)
{
lean_ctor_set(x_14, 0, x_20);
x_21 = x_14;
goto block_22;
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_20);
x_21 = x_23;
goto block_22;
}
block_22:
{
return x_21;
}
}
}
}
else
{
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_st_ref_get(x_9);
x_27 = lean_st_ref_get(x_5);
x_28 = lean_ctor_get(x_27, 0);
lean_inc_ref(x_28);
lean_dec(x_27);
x_29 = lean_box(1);
x_30 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_31 = 0;
x_32 = lean_unsigned_to_nat(0u);
x_33 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_33);
lean_ctor_set(x_35, 4, x_34);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*7, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 1, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 2, x_31);
lean_ctor_set_uint8(x_35, sizeof(void*)*7 + 3, x_11);
x_36 = lean_unsigned_to_nat(32u);
x_37 = lean_mk_empty_array_with_capacity(x_36);
lean_dec_ref(x_37);
x_38 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_39 = lean_st_mk_ref(x_38);
x_40 = lean_ctor_get(x_26, 0);
lean_inc_ref(x_40);
lean_dec(x_26);
x_41 = l_Lean_getStructureInfo(x_40, x_1);
x_42 = lean_ctor_get(x_41, 1);
lean_inc_ref(x_42);
lean_dec_ref(x_41);
x_43 = lean_box(0);
x_44 = lean_array_get(x_43, x_42, x_2);
lean_dec(x_2);
lean_dec_ref(x_42);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_39);
x_45 = l_Lean_Meta_mkProjection(x_3, x_44, x_35, x_39, x_8, x_9);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec_ref(x_45);
x_47 = lean_st_ref_get(x_39);
lean_dec(x_39);
lean_dec(x_47);
x_48 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_46, x_4, x_5, x_6, x_7, x_8, x_9);
return x_48;
}
else
{
lean_dec(x_39);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
lean_dec_ref(x_45);
x_50 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_49, x_4, x_5, x_6, x_7, x_8, x_9);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; uint8_t x_58; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
x_51 = lean_ctor_get(x_45, 0);
x_58 = !lean_is_exclusive(x_45);
if (x_58 == 0)
{
x_52 = x_45;
x_53 = x_58;
goto block_57;
}
else
{
lean_inc(x_51);
lean_dec(x_45);
x_52 = lean_box(0);
x_53 = x_58;
goto block_57;
}
block_57:
{
lean_object* x_54; 
if (x_53 == 0)
{
x_54 = x_52;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = ((lean_object*)(l_Lean_isCtor_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__38___closed__2));
x_2 = lean_unsigned_to_nat(57u);
x_3 = lean_unsigned_to_nat(464u);
x_4 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__0));
x_5 = ((lean_object*)(l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___lam__0___closed__0));
x_6 = l_mkPanicMessageWithDecl(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_100; 
x_34 = lean_ctor_get(x_6, 0);
x_35 = lean_ctor_get(x_6, 1);
x_36 = lean_ctor_get(x_6, 2);
x_37 = lean_ctor_get(x_6, 3);
x_38 = lean_ctor_get(x_6, 4);
x_39 = lean_ctor_get(x_6, 5);
x_40 = lean_ctor_get(x_6, 6);
x_41 = lean_ctor_get(x_6, 7);
x_42 = lean_ctor_get(x_6, 8);
x_43 = lean_ctor_get(x_6, 9);
x_44 = lean_ctor_get(x_6, 10);
x_45 = lean_ctor_get(x_6, 11);
x_46 = lean_ctor_get_uint8(x_6, sizeof(void*)*14);
x_47 = lean_ctor_get(x_6, 12);
x_48 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_49 = lean_ctor_get(x_6, 13);
x_100 = !lean_is_exclusive(x_6);
if (x_100 == 0)
{
x_50 = x_6;
x_51 = x_100;
goto block_99;
}
else
{
lean_inc(x_49);
lean_inc(x_47);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_6);
x_50 = lean_box(0);
x_51 = x_100;
goto block_99;
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_st_ref_set(x_10, x_11);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_9);
return x_13;
}
block_33:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_take(x_16);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*6);
if (x_18 == 0)
{
lean_dec_ref(x_1);
x_9 = x_15;
x_10 = x_16;
x_11 = x_17;
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_32; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 2);
x_22 = lean_ctor_get(x_17, 3);
x_23 = lean_ctor_get(x_17, 4);
x_24 = lean_ctor_get(x_17, 5);
x_32 = !lean_is_exclusive(x_17);
if (x_32 == 0)
{
x_25 = x_17;
x_26 = x_32;
goto block_31;
}
else
{
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_25 = lean_box(0);
x_26 = x_32;
goto block_31;
}
block_31:
{
lean_object* x_27; lean_object* x_28; 
lean_inc(x_15);
x_27 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(x_20, x_1, x_15);
if (x_26 == 0)
{
lean_ctor_set(x_25, 1, x_27);
x_28 = x_25;
goto block_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_30, 0, x_19);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_21);
lean_ctor_set(x_30, 3, x_22);
lean_ctor_set(x_30, 4, x_23);
lean_ctor_set(x_30, 5, x_24);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_18);
x_28 = x_30;
goto block_29;
}
block_29:
{
x_9 = x_15;
x_10 = x_16;
x_11 = x_28;
goto block_14;
}
}
}
}
block_99:
{
uint8_t x_52; 
x_52 = lean_nat_dec_eq(x_37, x_38);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_st_ref_get(x_3);
x_54 = lean_ctor_get(x_53, 1);
lean_inc_ref(x_54);
lean_dec(x_53);
x_55 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_54, x_1);
if (lean_obj_tag(x_55) == 1)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_63; 
lean_del_object(x_50);
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_56 = lean_ctor_get(x_55, 0);
x_63 = !lean_is_exclusive(x_55);
if (x_63 == 0)
{
x_57 = x_55;
x_58 = x_63;
goto block_62;
}
else
{
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = x_63;
goto block_62;
}
block_62:
{
lean_object* x_59; 
if (x_58 == 0)
{
lean_ctor_set_tag(x_57, 0);
x_59 = x_57;
goto block_60;
}
else
{
lean_object* x_61; 
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_56);
x_59 = x_61;
goto block_60;
}
block_60:
{
return x_59;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_55);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_37, x_64);
lean_dec(x_37);
if (x_51 == 0)
{
lean_ctor_set(x_50, 3, x_65);
x_66 = x_50;
goto block_96;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_97, 0, x_34);
lean_ctor_set(x_97, 1, x_35);
lean_ctor_set(x_97, 2, x_36);
lean_ctor_set(x_97, 3, x_65);
lean_ctor_set(x_97, 4, x_38);
lean_ctor_set(x_97, 5, x_39);
lean_ctor_set(x_97, 6, x_40);
lean_ctor_set(x_97, 7, x_41);
lean_ctor_set(x_97, 8, x_42);
lean_ctor_set(x_97, 9, x_43);
lean_ctor_set(x_97, 10, x_44);
lean_ctor_set(x_97, 11, x_45);
lean_ctor_set(x_97, 12, x_47);
lean_ctor_set(x_97, 13, x_49);
lean_ctor_set_uint8(x_97, sizeof(void*)*14, x_46);
lean_ctor_set_uint8(x_97, sizeof(void*)*14 + 1, x_48);
x_66 = x_97;
goto block_96;
}
block_96:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
lean_dec_ref(x_66);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
x_67 = lean_ctor_get(x_1, 0);
x_68 = lean_st_ref_get(x_3);
x_69 = lean_ctor_get(x_68, 5);
lean_inc(x_69);
lean_dec(x_68);
x_70 = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Compiler_LCNF_ToLCNF_applyToAny_spec__0___redArg(x_67, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; 
lean_inc(x_67);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_67);
x_15 = x_71;
x_16 = x_3;
goto block_33;
}
else
{
lean_object* x_72; 
x_72 = lean_box(0);
x_15 = x_72;
x_16 = x_3;
goto block_33;
}
}
case 4:
{
lean_object* x_73; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_73 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_66, x_7);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_15 = x_74;
x_16 = x_3;
goto block_33;
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_73;
}
}
case 5:
{
lean_object* x_75; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_75 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_2, x_3, x_4, x_5, x_66, x_7);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_15 = x_76;
x_16 = x_3;
goto block_33;
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_75;
}
}
case 6:
{
lean_object* x_77; 
lean_inc(x_3);
lean_inc_ref(x_1);
x_77 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_2, x_3, x_4, x_5, x_66, x_7);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_15 = x_78;
x_16 = x_3;
goto block_33;
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_77;
}
}
case 8:
{
lean_object* x_79; lean_object* x_80; 
x_79 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_visitLambda___redArg___closed__0));
lean_inc(x_3);
lean_inc_ref(x_1);
x_80 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_79, x_2, x_3, x_4, x_5, x_66, x_7);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
lean_dec_ref(x_80);
x_15 = x_81;
x_16 = x_3;
goto block_33;
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_80;
}
}
case 9:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_82);
x_83 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLit___redArg(x_82, x_3, x_4, x_5, x_66, x_7);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
lean_dec_ref(x_83);
x_15 = x_84;
x_16 = x_3;
goto block_33;
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_83;
}
}
case 10:
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_inc_ref(x_85);
x_86 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_85, x_2, x_3, x_4, x_5, x_66, x_7);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
lean_dec_ref(x_86);
x_15 = x_87;
x_16 = x_3;
goto block_33;
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_86;
}
}
case 11:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_1, 0);
x_89 = lean_ctor_get(x_1, 1);
x_90 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_inc_ref(x_90);
lean_inc(x_89);
lean_inc(x_88);
x_91 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_88, x_89, x_90, x_2, x_3, x_4, x_5, x_66, x_7);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec_ref(x_91);
x_15 = x_92;
x_16 = x_3;
goto block_33;
}
else
{
lean_dec_ref(x_1);
lean_dec(x_3);
return x_91;
}
}
default: 
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_obj_once(&l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1, &l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1_once, _init_l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___closed__1);
lean_inc(x_3);
x_94 = l_panic___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__2(x_93, x_2, x_3, x_4, x_5, x_66, x_7);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
lean_dec_ref(x_94);
x_15 = x_95;
x_16 = x_3;
goto block_33;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_94;
}
}
}
}
}
}
else
{
lean_object* x_98; 
lean_del_object(x_50);
lean_dec_ref(x_49);
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec_ref(x_36);
lean_dec_ref(x_35);
lean_dec_ref(x_34);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_98 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg(x_39);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_108; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_ctor_get(x_6, 2);
x_12 = lean_ctor_get(x_6, 3);
x_13 = lean_ctor_get(x_6, 4);
x_14 = lean_ctor_get(x_6, 5);
x_15 = lean_ctor_get(x_6, 6);
x_16 = lean_ctor_get(x_6, 7);
x_17 = lean_ctor_get(x_6, 8);
x_18 = lean_ctor_get(x_6, 9);
x_19 = lean_ctor_get(x_6, 10);
x_20 = lean_ctor_get(x_6, 11);
x_21 = lean_ctor_get_uint8(x_6, sizeof(void*)*14);
x_22 = lean_ctor_get(x_6, 12);
x_23 = lean_ctor_get_uint8(x_6, sizeof(void*)*14 + 1);
x_24 = lean_ctor_get(x_6, 13);
x_108 = !lean_is_exclusive(x_6);
if (x_108 == 0)
{
x_25 = x_6;
x_26 = x_108;
goto block_107;
}
else
{
lean_inc(x_24);
lean_inc(x_22);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_6);
x_25 = lean_box(0);
x_26 = x_108;
goto block_107;
}
block_107:
{
uint8_t x_27; 
x_27 = lean_nat_dec_eq(x_12, x_13);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = l_Lean_Compiler_LCNF_ToLCNF_isLCProof(x_1);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_29 = lean_st_ref_get(x_3);
x_30 = lean_ctor_get(x_29, 0);
lean_inc_ref(x_30);
lean_dec(x_29);
x_31 = lean_box(1);
x_32 = l_Lean_Meta_instInhabitedConfigWithKey___private__1;
x_33 = lean_unsigned_to_nat(0u);
x_34 = ((lean_object*)(l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__0));
x_35 = lean_box(0);
x_36 = 1;
x_37 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_30);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_35);
lean_ctor_set(x_37, 5, x_33);
lean_ctor_set(x_37, 6, x_35);
lean_ctor_set_uint8(x_37, sizeof(void*)*7, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 1, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 2, x_27);
lean_ctor_set_uint8(x_37, sizeof(void*)*7 + 3, x_36);
x_38 = lean_unsigned_to_nat(32u);
x_39 = lean_mk_empty_array_with_capacity(x_38);
lean_dec_ref(x_39);
x_40 = lean_obj_once(&l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5, &l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5_once, _init_l_Lean_Compiler_LCNF_ToLCNF_liftMetaM___redArg___closed__5);
x_41 = lean_st_mk_ref(x_40);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_add(x_12, x_42);
lean_dec(x_12);
if (x_26 == 0)
{
lean_ctor_set(x_25, 3, x_43);
x_44 = x_25;
goto block_102;
}
else
{
lean_object* x_103; 
x_103 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_103, 0, x_9);
lean_ctor_set(x_103, 1, x_10);
lean_ctor_set(x_103, 2, x_11);
lean_ctor_set(x_103, 3, x_43);
lean_ctor_set(x_103, 4, x_13);
lean_ctor_set(x_103, 5, x_14);
lean_ctor_set(x_103, 6, x_15);
lean_ctor_set(x_103, 7, x_16);
lean_ctor_set(x_103, 8, x_17);
lean_ctor_set(x_103, 9, x_18);
lean_ctor_set(x_103, 10, x_19);
lean_ctor_set(x_103, 11, x_20);
lean_ctor_set(x_103, 12, x_22);
lean_ctor_set(x_103, 13, x_24);
lean_ctor_set_uint8(x_103, sizeof(void*)*14, x_21);
lean_ctor_set_uint8(x_103, sizeof(void*)*14 + 1, x_23);
x_44 = x_103;
goto block_102;
}
block_102:
{
lean_object* x_45; uint8_t x_46; lean_object* x_70; lean_object* x_90; 
lean_inc(x_7);
lean_inc_ref(x_44);
lean_inc(x_41);
lean_inc_ref(x_1);
x_90 = lean_infer_type(x_1, x_37, x_41, x_44, x_7);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec_ref(x_90);
x_92 = lean_st_ref_get(x_41);
lean_dec(x_41);
lean_dec(x_92);
x_70 = x_91;
goto block_89;
}
else
{
lean_dec(x_41);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_93; 
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec_ref(x_90);
x_70 = x_93;
goto block_89;
}
else
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_101; 
lean_dec_ref(x_44);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_94 = lean_ctor_get(x_90, 0);
x_101 = !lean_is_exclusive(x_90);
if (x_101 == 0)
{
x_95 = x_90;
x_96 = x_101;
goto block_100;
}
else
{
lean_inc(x_94);
lean_dec(x_90);
x_95 = lean_box(0);
x_96 = x_101;
goto block_100;
}
block_100:
{
lean_object* x_97; 
if (x_96 == 0)
{
x_97 = x_95;
goto block_98;
}
else
{
lean_object* x_99; 
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_94);
x_97 = x_99;
goto block_98;
}
block_98:
{
return x_97;
}
}
}
}
block_69:
{
if (x_46 == 0)
{
lean_object* x_47; 
lean_inc(x_7);
lean_inc_ref(x_44);
x_47 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_isTypeFormerType___redArg(x_45, x_3, x_44, x_7);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_58; 
x_48 = lean_ctor_get(x_47, 0);
x_58 = !lean_is_exclusive(x_47);
if (x_58 == 0)
{
x_49 = x_47;
x_50 = x_58;
goto block_57;
}
else
{
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_box(0);
x_50 = x_58;
goto block_57;
}
block_57:
{
uint8_t x_51; 
x_51 = lean_unbox(x_48);
lean_dec(x_48);
if (x_51 == 0)
{
lean_object* x_52; 
lean_del_object(x_49);
x_52 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_2, x_3, x_4, x_5, x_44, x_7);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec_ref(x_44);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_53 = lean_box(0);
if (x_50 == 0)
{
lean_ctor_set(x_49, 0, x_53);
x_54 = x_49;
goto block_55;
}
else
{
lean_object* x_56; 
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_53);
x_54 = x_56;
goto block_55;
}
block_55:
{
return x_54;
}
}
}
}
else
{
lean_object* x_59; lean_object* x_60; uint8_t x_61; uint8_t x_66; 
lean_dec_ref(x_44);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_59 = lean_ctor_get(x_47, 0);
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
x_60 = x_47;
x_61 = x_66;
goto block_65;
}
else
{
lean_inc(x_59);
lean_dec(x_47);
x_60 = lean_box(0);
x_61 = x_66;
goto block_65;
}
block_65:
{
lean_object* x_62; 
if (x_61 == 0)
{
x_62 = x_60;
goto block_63;
}
else
{
lean_object* x_64; 
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_59);
x_62 = x_64;
goto block_63;
}
block_63:
{
return x_62;
}
}
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
return x_68;
}
}
block_89:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_st_ref_get(x_3);
x_72 = lean_ctor_get(x_71, 0);
lean_inc_ref(x_72);
lean_dec(x_71);
x_73 = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(x_73, 0, x_32);
lean_ctor_set(x_73, 1, x_31);
lean_ctor_set(x_73, 2, x_72);
lean_ctor_set(x_73, 3, x_34);
lean_ctor_set(x_73, 4, x_35);
lean_ctor_set(x_73, 5, x_33);
lean_ctor_set(x_73, 6, x_35);
lean_ctor_set_uint8(x_73, sizeof(void*)*7, x_27);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 1, x_27);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 2, x_27);
lean_ctor_set_uint8(x_73, sizeof(void*)*7 + 3, x_36);
x_74 = lean_st_mk_ref(x_40);
lean_inc(x_7);
lean_inc_ref(x_44);
lean_inc(x_74);
lean_inc_ref(x_70);
x_75 = l_Lean_Meta_isProp(x_70, x_73, x_74, x_44, x_7);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
lean_dec_ref(x_75);
x_77 = lean_st_ref_get(x_74);
lean_dec(x_74);
lean_dec(x_77);
x_78 = lean_unbox(x_76);
lean_dec(x_76);
x_45 = x_70;
x_46 = x_78;
goto block_69;
}
else
{
lean_dec(x_74);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_75, 0);
lean_inc(x_79);
lean_dec_ref(x_75);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
x_45 = x_70;
x_46 = x_80;
goto block_69;
}
else
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; uint8_t x_88; 
lean_dec_ref(x_70);
lean_dec_ref(x_44);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_81 = lean_ctor_get(x_75, 0);
x_88 = !lean_is_exclusive(x_75);
if (x_88 == 0)
{
x_82 = x_75;
x_83 = x_88;
goto block_87;
}
else
{
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_box(0);
x_83 = x_88;
goto block_87;
}
block_87:
{
lean_object* x_84; 
if (x_83 == 0)
{
x_84 = x_82;
goto block_85;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_81);
x_84 = x_86;
goto block_85;
}
block_85:
{
return x_84;
}
}
}
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_del_object(x_25);
lean_dec_ref(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_del_object(x_25);
lean_dec_ref(x_24);
lean_dec(x_22);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec_ref(x_10);
lean_dec_ref(x_9);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
x_106 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg(x_14);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitFalseRec(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLcUnreachable(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__12(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_etaIfUnderApplied(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitQuotLift(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__10(x_11, x_12, x_3, x_13, x_5, x_6, x_7, x_8, x_9);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec_ref(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAndIffRecCore(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_Expr_withAppAux___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__13(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_6);
x_14 = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___redArg(x_1, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitEqRec(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitHEqRec(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLambda(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___redArg(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppDefaultConst(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProj(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitLet(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAppArg(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitMData(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___redArg(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_throwMaxRecDepthAt___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__3(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___redArg(x_1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_getProjectionFnInfo_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitApp_spec__11(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___redArg(x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_throwError___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__19(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
x_11 = l_Lean_Meta_forallTelescope___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__21(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___redArg(x_1, x_4, x_5, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
x_13 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitNoConfusion_spec__20(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__24(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__25(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Init_WFExtrinsicFix_0__WellFounded_opaqueFix_u2082___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__25___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCases_spec__26(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec_ref(x_13);
lean_dec(x_12);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29(size_t x_1, size_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_4);
x_14 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitAlt_spec__29(x_11, x_12, x_3, x_13, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_14;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_15; 
x_15 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___redArg(x_1, x_2, x_5, x_6, x_8, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_8);
x_16 = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_mkOverApplication_spec__31(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_7);
x_15 = l_Array_mapFinIdxM_map___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCtor_spec__39(x_1, x_2, x_3, x_4, x_5, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
lean_dec_ref(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11(x_1, x_2, x_7, x_8, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29(lean_object* x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___redArg(x_2, x_3, x_4, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; lean_object* x_9; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__29(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_4);
lean_dec_ref(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__1_spec__13_spec__32(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28_spec__43(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitCore_spec__0_spec__11_spec__28_spec__43___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
x_13 = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___redArg(x_1, x_2, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
x_11 = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__50_spec__51(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
x_12 = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00__private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visitProjFn_spec__17_spec__25_spec__38_spec__49_spec__51(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
x_9 = l___private_Lean_Compiler_LCNF_ToLCNF_0__Lean_Compiler_LCNF_ToLCNF_toLCNF_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec_ref(x_9);
x_11 = l_Lean_Compiler_LCNF_ToLCNF_toCode___redArg(x_10, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_19; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_9, 0);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
x_13 = x_9;
x_14 = x_19;
goto block_18;
}
else
{
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = x_19;
goto block_18;
}
block_18:
{
lean_object* x_15; 
if (x_14 == 0)
{
x_15 = x_13;
goto block_16;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_12);
x_15 = x_17;
goto block_16;
}
block_16:
{
return x_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
x_10 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ToLCNF_toLCNF___lam__0___boxed), 8, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Compiler_LCNF_ToLCNF_run___redArg(x_7, x_2, x_3, x_4, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToLCNF_toLCNF___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToLCNF_toLCNF(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
lean_object* runtime_initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_CasesInfo(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* runtime_initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
lean_object* runtime_initialize_Lean_OriginalConstKind(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_AppBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_CSimpAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_ImplementedByAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Bind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NeverExtractAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_CasesInfo(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_WHNF(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_NoncomputableAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Format_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_OriginalConstKind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement_default);
l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement = _init_l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement();
lean_mark_persistent(l_Lean_Compiler_LCNF_ToLCNF_instInhabitedElement);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin);
lean_object* initialize_Lean_Compiler_CSimpAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NeverExtractAttr(uint8_t builtin);
lean_object* initialize_Lean_Meta_CasesInfo(uint8_t builtin);
lean_object* initialize_Lean_Meta_WHNF(uint8_t builtin);
lean_object* initialize_Lean_Compiler_NoncomputableAttr(uint8_t builtin);
lean_object* initialize_Lean_Compiler_LCNF_Util(uint8_t builtin);
lean_object* initialize_Init_Data_Format_Macro(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
lean_object* initialize_Lean_OriginalConstKind(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ToLCNF(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_CSimpAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_ImplementedByAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NeverExtractAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_CasesInfo(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_WHNF(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_NoncomputableAttr(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Util(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Format_Macro(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_OriginalConstKind(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Compiler_LCNF_ToLCNF(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Compiler_LCNF_ToLCNF(builtin)
;
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Compiler_LCNF_ToLCNF(builtin);
}
#ifdef __cplusplus
}
#endif
