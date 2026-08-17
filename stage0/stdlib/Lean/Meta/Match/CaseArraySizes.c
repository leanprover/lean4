// Lean compiler output
// Module: Lean.Meta.Match.CaseArraySizes
// Imports: public import Lean.Meta.Basic public import Lean.Meta.Tactic.FVarSubst import Lean.Meta.Match.CaseValues import Lean.Meta.Tactic.Subst
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Meta_mkLt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkDecideProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_Meta_introNCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore(lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_FVarSubst_get(lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_mkFVar(lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assertExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_caseValues(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0 = (const lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value),((lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1 = (const lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default = (const lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_instInhabitedCaseArraySizesSubgoal = (const lean_object*)&l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_getArrayArgType___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Array"};
static const lean_object* l_Lean_Meta_getArrayArgType___closed__0 = (const lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value;
static const lean_ctor_object l_Lean_Meta_getArrayArgType___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_object* l_Lean_Meta_getArrayArgType___closed__1 = (const lean_object*)&l_Lean_Meta_getArrayArgType___closed__1_value;
static const lean_string_object l_Lean_Meta_getArrayArgType___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "array expected"};
static const lean_object* l_Lean_Meta_getArrayArgType___closed__2 = (const lean_object*)&l_Lean_Meta_getArrayArgType___closed__2_value;
static lean_once_cell_t l_Lean_Meta_getArrayArgType___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_getArrayArgType___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "getLit"};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__0_value),LEAN_SCALAR_PTR_LITERAL(203, 31, 150, 206, 23, 239, 28, 61)}};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "toArrayLit_eq"};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value_aux_0),((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 54, 254, 215, 42, 180, 33, 232)}};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1_value;
static const lean_string_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "hEqALit"};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value;
static const lean_ctor_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__2_value),LEAN_SCALAR_PTR_LITERAL(144, 218, 54, 212, 216, 192, 54, 198)}};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0 = (const lean_object*)&l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_caseArraySizes___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "aSize"};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Meta_caseArraySizes___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(177, 102, 98, 152, 210, 104, 173, 219)}};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__1 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__1_value;
static const lean_string_object l_Lean_Meta_caseArraySizes___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_caseArraySizes___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Meta_caseArraySizes___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__4;
static const lean_string_object l_Lean_Meta_caseArraySizes___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__5_value;
static const lean_ctor_object l_Lean_Meta_caseArraySizes___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__5_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_Lean_Meta_caseArraySizes___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_caseArraySizes___lam__0___closed__6_value;
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_caseArraySizes___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "size"};
static const lean_object* l_Lean_Meta_caseArraySizes___closed__0 = (const lean_object*)&l_Lean_Meta_caseArraySizes___closed__0_value;
static const lean_ctor_object l_Lean_Meta_caseArraySizes___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_getArrayArgType___closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 46, 193, 1, 46, 43, 107, 121)}};
static const lean_ctor_object l_Lean_Meta_caseArraySizes___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Meta_caseArraySizes___closed__1_value_aux_0),((lean_object*)&l_Lean_Meta_caseArraySizes___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 164, 37, 176, 250, 127, 194, 229)}};
static const lean_object* l_Lean_Meta_caseArraySizes___closed__1 = (const lean_object*)&l_Lean_Meta_caseArraySizes___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(lean_object* v_msgData_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; lean_object* v_env_16_; lean_object* v___x_17_; lean_object* v_mctx_18_; lean_object* v_lctx_19_; lean_object* v_options_20_; lean_object* v___x_21_; lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_15_ = lean_st_ref_get(v___y_13_);
v_env_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_env_16_);
lean_dec(v___x_15_);
v___x_17_ = lean_st_ref_get(v___y_11_);
v_mctx_18_ = lean_ctor_get(v___x_17_, 0);
lean_inc_ref(v_mctx_18_);
lean_dec(v___x_17_);
v_lctx_19_ = lean_ctor_get(v___y_10_, 2);
v_options_20_ = lean_ctor_get(v___y_12_, 2);
lean_inc_ref(v_options_20_);
lean_inc_ref(v_lctx_19_);
v___x_21_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_21_, 0, v_env_16_);
lean_ctor_set(v___x_21_, 1, v_mctx_18_);
lean_ctor_set(v___x_21_, 2, v_lctx_19_);
lean_ctor_set(v___x_21_, 3, v_options_20_);
v___x_22_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_22_, 0, v___x_21_);
lean_ctor_set(v___x_22_, 1, v_msgData_9_);
v___x_23_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_23_, 0, v___x_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0___boxed(lean_object* v_msgData_24_, lean_object* v___y_25_, lean_object* v___y_26_, lean_object* v___y_27_, lean_object* v___y_28_, lean_object* v___y_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msgData_24_, v___y_25_, v___y_26_, v___y_27_, v___y_28_);
lean_dec(v___y_28_);
lean_dec_ref(v___y_27_);
lean_dec(v___y_26_);
lean_dec_ref(v___y_25_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(lean_object* v_msg_31_, lean_object* v___y_32_, lean_object* v___y_33_, lean_object* v___y_34_, lean_object* v___y_35_){
_start:
{
lean_object* v_ref_37_; lean_object* v___x_38_; lean_object* v_a_39_; lean_object* v___x_41_; uint8_t v_isShared_42_; uint8_t v_isSharedCheck_47_; 
v_ref_37_ = lean_ctor_get(v___y_34_, 5);
v___x_38_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msg_31_, v___y_32_, v___y_33_, v___y_34_, v___y_35_);
v_a_39_ = lean_ctor_get(v___x_38_, 0);
v_isSharedCheck_47_ = !lean_is_exclusive(v___x_38_);
if (v_isSharedCheck_47_ == 0)
{
v___x_41_ = v___x_38_;
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
else
{
lean_inc(v_a_39_);
lean_dec(v___x_38_);
v___x_41_ = lean_box(0);
v_isShared_42_ = v_isSharedCheck_47_;
goto v_resetjp_40_;
}
v_resetjp_40_:
{
lean_object* v___x_43_; lean_object* v___x_45_; 
lean_inc(v_ref_37_);
v___x_43_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_43_, 0, v_ref_37_);
lean_ctor_set(v___x_43_, 1, v_a_39_);
if (v_isShared_42_ == 0)
{
lean_ctor_set_tag(v___x_41_, 1);
lean_ctor_set(v___x_41_, 0, v___x_43_);
v___x_45_ = v___x_41_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_46_; 
v_reuseFailAlloc_46_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_46_, 0, v___x_43_);
v___x_45_ = v_reuseFailAlloc_46_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
return v___x_45_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg___boxed(lean_object* v_msg_48_, lean_object* v___y_49_, lean_object* v___y_50_, lean_object* v___y_51_, lean_object* v___y_52_, lean_object* v___y_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_48_, v___y_49_, v___y_50_, v___y_51_, v___y_52_);
lean_dec(v___y_52_);
lean_dec_ref(v___y_51_);
lean_dec(v___y_50_);
lean_dec_ref(v___y_49_);
return v_res_54_;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__3(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = ((lean_object*)(l_Lean_Meta_getArrayArgType___closed__2));
v___x_60_ = l_Lean_stringToMessageData(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType(lean_object* v_a_61_, lean_object* v_a_62_, lean_object* v_a_63_, lean_object* v_a_64_, lean_object* v_a_65_){
_start:
{
lean_object* v___x_67_; 
lean_inc(v_a_65_);
lean_inc_ref(v_a_64_);
lean_inc(v_a_63_);
lean_inc_ref(v_a_62_);
lean_inc_ref(v_a_61_);
v___x_67_ = lean_infer_type(v_a_61_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_67_) == 0)
{
lean_object* v_a_68_; lean_object* v___x_69_; 
v_a_68_ = lean_ctor_get(v___x_67_, 0);
lean_inc(v_a_68_);
lean_dec_ref_known(v___x_67_, 1);
v___x_69_ = l_Lean_Meta_whnfD(v_a_68_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
if (lean_obj_tag(v___x_69_) == 0)
{
lean_object* v_a_70_; lean_object* v___x_72_; uint8_t v_isShared_73_; uint8_t v_isSharedCheck_94_; 
v_a_70_ = lean_ctor_get(v___x_69_, 0);
v_isSharedCheck_94_ = !lean_is_exclusive(v___x_69_);
if (v_isSharedCheck_94_ == 0)
{
v___x_72_ = v___x_69_;
v_isShared_73_ = v_isSharedCheck_94_;
goto v_resetjp_71_;
}
else
{
lean_inc(v_a_70_);
lean_dec(v___x_69_);
v___x_72_ = lean_box(0);
v_isShared_73_ = v_isSharedCheck_94_;
goto v_resetjp_71_;
}
v_resetjp_71_:
{
lean_object* v___x_79_; lean_object* v___x_80_; uint8_t v___x_81_; 
v___x_79_ = ((lean_object*)(l_Lean_Meta_getArrayArgType___closed__1));
v___x_80_ = lean_unsigned_to_nat(1u);
v___x_81_ = l_Lean_Expr_isAppOfArity(v_a_70_, v___x_79_, v___x_80_);
if (v___x_81_ == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_del_object(v___x_72_);
lean_dec(v_a_70_);
v___x_82_ = lean_obj_once(&l_Lean_Meta_getArrayArgType___closed__3, &l_Lean_Meta_getArrayArgType___closed__3_once, _init_l_Lean_Meta_getArrayArgType___closed__3);
v___x_83_ = l_Lean_indentExpr(v_a_61_);
v___x_84_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_82_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v___x_84_, v_a_62_, v_a_63_, v_a_64_, v_a_65_);
v_a_86_ = lean_ctor_get(v___x_85_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_85_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_85_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_dec(v___x_85_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
else
{
lean_dec_ref(v_a_61_);
goto v___jp_74_;
}
v___jp_74_:
{
lean_object* v___x_75_; lean_object* v___x_77_; 
v___x_75_ = l_Lean_Expr_appArg_x21(v_a_70_);
lean_dec(v_a_70_);
if (v_isShared_73_ == 0)
{
lean_ctor_set(v___x_72_, 0, v___x_75_);
v___x_77_ = v___x_72_;
goto v_reusejp_76_;
}
else
{
lean_object* v_reuseFailAlloc_78_; 
v_reuseFailAlloc_78_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_78_, 0, v___x_75_);
v___x_77_ = v_reuseFailAlloc_78_;
goto v_reusejp_76_;
}
v_reusejp_76_:
{
return v___x_77_;
}
}
}
}
else
{
lean_dec_ref(v_a_61_);
return v___x_69_;
}
}
else
{
lean_dec_ref(v_a_61_);
return v___x_67_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType___boxed(lean_object* v_a_95_, lean_object* v_a_96_, lean_object* v_a_97_, lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_Lean_Meta_getArrayArgType(v_a_95_, v_a_96_, v_a_97_, v_a_98_, v_a_99_);
lean_dec(v_a_99_);
lean_dec_ref(v_a_98_);
lean_dec(v_a_97_);
lean_dec_ref(v_a_96_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(lean_object* v_00_u03b1_102_, lean_object* v_msg_103_, lean_object* v___y_104_, lean_object* v___y_105_, lean_object* v___y_106_, lean_object* v___y_107_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_103_, v___y_104_, v___y_105_, v___y_106_, v___y_107_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___boxed(lean_object* v_00_u03b1_110_, lean_object* v_msg_111_, lean_object* v___y_112_, lean_object* v___y_113_, lean_object* v___y_114_, lean_object* v___y_115_, lean_object* v___y_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(v_00_u03b1_110_, v_msg_111_, v___y_112_, v___y_113_, v___y_114_, v___y_115_);
lean_dec(v___y_115_);
lean_dec_ref(v___y_114_);
lean_dec(v___y_113_);
lean_dec_ref(v___y_112_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object* v_a_122_, lean_object* v_i_123_, lean_object* v_n_124_, lean_object* v_h_125_, lean_object* v_a_126_, lean_object* v_a_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_131_ = l_Lean_mkRawNatLit(v_i_123_);
v___x_132_ = l_Lean_mkRawNatLit(v_n_124_);
lean_inc_ref(v___x_131_);
v___x_133_ = l_Lean_Meta_mkLt(v___x_131_, v___x_132_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_133_) == 0)
{
lean_object* v_a_134_; lean_object* v___x_135_; 
v_a_134_ = lean_ctor_get(v___x_133_, 0);
lean_inc(v_a_134_);
lean_dec_ref_known(v___x_133_, 1);
v___x_135_ = l_Lean_Meta_mkDecideProof(v_a_134_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
if (lean_obj_tag(v___x_135_) == 0)
{
lean_object* v_a_136_; lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_a_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_a_136_);
lean_dec_ref_known(v___x_135_, 1);
v___x_137_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1));
v___x_138_ = lean_unsigned_to_nat(4u);
v___x_139_ = lean_mk_empty_array_with_capacity(v___x_138_);
v___x_140_ = lean_array_push(v___x_139_, v_a_122_);
v___x_141_ = lean_array_push(v___x_140_, v___x_131_);
v___x_142_ = lean_array_push(v___x_141_, v_h_125_);
v___x_143_ = lean_array_push(v___x_142_, v_a_136_);
v___x_144_ = l_Lean_Meta_mkAppM(v___x_137_, v___x_143_, v_a_126_, v_a_127_, v_a_128_, v_a_129_);
return v___x_144_;
}
else
{
lean_dec_ref(v___x_131_);
lean_dec_ref(v_h_125_);
lean_dec_ref(v_a_122_);
return v___x_135_;
}
}
else
{
lean_dec_ref(v___x_131_);
lean_dec_ref(v_h_125_);
lean_dec_ref(v_a_122_);
return v___x_133_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___boxed(lean_object* v_a_145_, lean_object* v_i_146_, lean_object* v_n_147_, lean_object* v_h_148_, lean_object* v_a_149_, lean_object* v_a_150_, lean_object* v_a_151_, lean_object* v_a_152_, lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_145_, v_i_146_, v_n_147_, v_h_148_, v_a_149_, v_a_150_, v_a_151_, v_a_152_);
lean_dec(v_a_152_);
lean_dec_ref(v_a_151_);
lean_dec(v_a_150_);
lean_dec_ref(v_a_149_);
return v_res_154_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(lean_object* v_mvarId_155_, lean_object* v_xs_156_, uint8_t v___x_157_, lean_object* v_args_158_, lean_object* v_a_159_, lean_object* v_heq_160_, lean_object* v___y_161_, lean_object* v___y_162_, lean_object* v___y_163_, lean_object* v___y_164_){
_start:
{
lean_object* v___x_166_; 
v___x_166_ = l_Lean_MVarId_getType(v_mvarId_155_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v_a_167_; lean_object* v___x_168_; uint8_t v___x_169_; uint8_t v___x_170_; lean_object* v___x_171_; 
v_a_167_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_a_167_);
lean_dec_ref_known(v___x_166_, 1);
v___x_168_ = lean_array_push(v_xs_156_, v_heq_160_);
v___x_169_ = 1;
v___x_170_ = 1;
v___x_171_ = l_Lean_Meta_mkForallFVars(v___x_168_, v_a_167_, v___x_157_, v___x_169_, v___x_169_, v___x_170_, v___y_161_, v___y_162_, v___y_163_, v___y_164_);
lean_dec_ref(v___x_168_);
if (lean_obj_tag(v___x_171_) == 0)
{
lean_object* v_a_172_; lean_object* v___x_174_; uint8_t v_isShared_175_; uint8_t v_isSharedCheck_181_; 
v_a_172_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_181_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_181_ == 0)
{
v___x_174_ = v___x_171_;
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
else
{
lean_inc(v_a_172_);
lean_dec(v___x_171_);
v___x_174_ = lean_box(0);
v_isShared_175_ = v_isSharedCheck_181_;
goto v_resetjp_173_;
}
v_resetjp_173_:
{
lean_object* v___x_176_; lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_176_ = lean_array_push(v_args_158_, v_a_159_);
v___x_177_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_177_, 0, v_a_172_);
lean_ctor_set(v___x_177_, 1, v___x_176_);
if (v_isShared_175_ == 0)
{
lean_ctor_set(v___x_174_, 0, v___x_177_);
v___x_179_ = v___x_174_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
else
{
lean_object* v_a_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_189_; 
lean_dec_ref(v_a_159_);
lean_dec_ref(v_args_158_);
v_a_182_ = lean_ctor_get(v___x_171_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_171_);
if (v_isSharedCheck_189_ == 0)
{
v___x_184_ = v___x_171_;
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_a_182_);
lean_dec(v___x_171_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_189_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_185_ == 0)
{
v___x_187_ = v___x_184_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v_a_182_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec_ref(v_heq_160_);
lean_dec_ref(v_a_159_);
lean_dec_ref(v_args_158_);
lean_dec_ref(v_xs_156_);
v_a_190_ = lean_ctor_get(v___x_166_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_166_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_166_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_166_);
v___x_192_ = lean_box(0);
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
v_resetjp_191_:
{
lean_object* v___x_195_; 
if (v_isShared_193_ == 0)
{
v___x_195_ = v___x_192_;
goto v_reusejp_194_;
}
else
{
lean_object* v_reuseFailAlloc_196_; 
v_reuseFailAlloc_196_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_196_, 0, v_a_190_);
v___x_195_ = v_reuseFailAlloc_196_;
goto v_reusejp_194_;
}
v_reusejp_194_:
{
return v___x_195_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(lean_object* v_mvarId_198_, lean_object* v_xs_199_, lean_object* v___x_200_, lean_object* v_args_201_, lean_object* v_a_202_, lean_object* v_heq_203_, lean_object* v___y_204_, lean_object* v___y_205_, lean_object* v___y_206_, lean_object* v___y_207_, lean_object* v___y_208_){
_start:
{
uint8_t v___x_1223__boxed_209_; lean_object* v_res_210_; 
v___x_1223__boxed_209_ = lean_unbox(v___x_200_);
v_res_210_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(v_mvarId_198_, v_xs_199_, v___x_1223__boxed_209_, v_args_201_, v_a_202_, v_heq_203_, v___y_204_, v___y_205_, v___y_206_, v___y_207_);
lean_dec(v___y_207_);
lean_dec_ref(v___y_206_);
lean_dec(v___y_205_);
lean_dec_ref(v___y_204_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_211_, lean_object* v_b_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v___x_218_; 
lean_inc(v___y_216_);
lean_inc_ref(v___y_215_);
lean_inc(v___y_214_);
lean_inc_ref(v___y_213_);
v___x_218_ = lean_apply_6(v_k_211_, v_b_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_, lean_box(0));
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_219_, lean_object* v_b_220_, lean_object* v___y_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(v_k_219_, v_b_220_, v___y_221_, v___y_222_, v___y_223_, v___y_224_);
lean_dec(v___y_224_);
lean_dec_ref(v___y_223_);
lean_dec(v___y_222_);
lean_dec_ref(v___y_221_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(lean_object* v_name_227_, uint8_t v_bi_228_, lean_object* v_type_229_, lean_object* v_k_230_, uint8_t v_kind_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v___f_237_; lean_object* v___x_238_; 
v___f_237_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_237_, 0, v_k_230_);
v___x_238_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_227_, v_bi_228_, v_type_229_, v___f_237_, v_kind_231_, v___y_232_, v___y_233_, v___y_234_, v___y_235_);
if (lean_obj_tag(v___x_238_) == 0)
{
lean_object* v_a_239_; lean_object* v___x_241_; uint8_t v_isShared_242_; uint8_t v_isSharedCheck_246_; 
v_a_239_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_246_ == 0)
{
v___x_241_ = v___x_238_;
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
else
{
lean_inc(v_a_239_);
lean_dec(v___x_238_);
v___x_241_ = lean_box(0);
v_isShared_242_ = v_isSharedCheck_246_;
goto v_resetjp_240_;
}
v_resetjp_240_:
{
lean_object* v___x_244_; 
if (v_isShared_242_ == 0)
{
v___x_244_ = v___x_241_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_a_239_);
v___x_244_ = v_reuseFailAlloc_245_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
return v___x_244_;
}
}
}
else
{
lean_object* v_a_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_254_; 
v_a_247_ = lean_ctor_get(v___x_238_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v___x_238_);
if (v_isSharedCheck_254_ == 0)
{
v___x_249_ = v___x_238_;
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_a_247_);
lean_dec(v___x_238_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_254_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_252_; 
if (v_isShared_250_ == 0)
{
v___x_252_ = v___x_249_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_a_247_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_255_, lean_object* v_bi_256_, lean_object* v_type_257_, lean_object* v_k_258_, lean_object* v_kind_259_, lean_object* v___y_260_, lean_object* v___y_261_, lean_object* v___y_262_, lean_object* v___y_263_, lean_object* v___y_264_){
_start:
{
uint8_t v_bi_boxed_265_; uint8_t v_kind_boxed_266_; lean_object* v_res_267_; 
v_bi_boxed_265_ = lean_unbox(v_bi_256_);
v_kind_boxed_266_ = lean_unbox(v_kind_259_);
v_res_267_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_255_, v_bi_boxed_265_, v_type_257_, v_k_258_, v_kind_boxed_266_, v___y_260_, v___y_261_, v___y_262_, v___y_263_);
lean_dec(v___y_263_);
lean_dec_ref(v___y_262_);
lean_dec(v___y_261_);
lean_dec_ref(v___y_260_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(lean_object* v_name_268_, lean_object* v_type_269_, lean_object* v_k_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_){
_start:
{
uint8_t v___x_276_; uint8_t v___x_277_; lean_object* v___x_278_; 
v___x_276_ = 0;
v___x_277_ = 0;
v___x_278_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_268_, v___x_276_, v_type_269_, v_k_270_, v___x_277_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg___boxed(lean_object* v_name_279_, lean_object* v_type_280_, lean_object* v_k_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_, lean_object* v___y_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_279_, v_type_280_, v_k_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
lean_dec(v___y_285_);
lean_dec_ref(v___y_284_);
lean_dec(v___y_283_);
lean_dec_ref(v___y_282_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed(lean_object* v_a_295_, lean_object* v_i_296_, lean_object* v_n_297_, lean_object* v_aSizeEqN_298_, lean_object* v_xs_299_, lean_object* v_args_300_, lean_object* v_mvarId_301_, lean_object* v_xNamePrefix_302_, lean_object* v_00_u03b1_303_, lean_object* v___x_304_, lean_object* v_xi_305_, lean_object* v___y_306_, lean_object* v___y_307_, lean_object* v___y_308_, lean_object* v___y_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(v_a_295_, v_i_296_, v_n_297_, v_aSizeEqN_298_, v_xs_299_, v_args_300_, v_mvarId_301_, v_xNamePrefix_302_, v_00_u03b1_303_, v___x_304_, v_xi_305_, v___y_306_, v___y_307_, v___y_308_, v___y_309_);
lean_dec(v___y_309_);
lean_dec_ref(v___y_308_);
lean_dec(v___y_307_);
lean_dec_ref(v___y_306_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object* v_mvarId_312_, lean_object* v_a_313_, lean_object* v_n_314_, lean_object* v_xNamePrefix_315_, lean_object* v_aSizeEqN_316_, lean_object* v_00_u03b1_317_, lean_object* v_i_318_, lean_object* v_xs_319_, lean_object* v_args_320_, lean_object* v_a_321_, lean_object* v_a_322_, lean_object* v_a_323_, lean_object* v_a_324_){
_start:
{
uint8_t v___x_326_; 
v___x_326_ = lean_nat_dec_lt(v_i_318_, v_n_314_);
if (v___x_326_ == 0)
{
lean_object* v___x_327_; lean_object* v___x_328_; 
lean_dec(v_i_318_);
lean_dec(v_xNamePrefix_315_);
lean_inc_ref(v_xs_319_);
v___x_327_ = lean_array_to_list(v_xs_319_);
v___x_328_ = l_Lean_Meta_mkArrayLit(v_00_u03b1_317_, v___x_327_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_328_) == 0)
{
lean_object* v_a_329_; lean_object* v___x_330_; 
v_a_329_ = lean_ctor_get(v___x_328_, 0);
lean_inc(v_a_329_);
lean_dec_ref_known(v___x_328_, 1);
lean_inc_ref(v_a_313_);
v___x_330_ = l_Lean_Meta_mkEq(v_a_313_, v_a_329_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_330_) == 0)
{
lean_object* v_a_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_a_331_ = lean_ctor_get(v___x_330_, 0);
lean_inc(v_a_331_);
lean_dec_ref_known(v___x_330_, 1);
v___x_332_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1));
v___x_333_ = l_Lean_mkRawNatLit(v_n_314_);
v___x_334_ = lean_unsigned_to_nat(3u);
v___x_335_ = lean_mk_empty_array_with_capacity(v___x_334_);
v___x_336_ = lean_array_push(v___x_335_, v_a_313_);
v___x_337_ = lean_array_push(v___x_336_, v___x_333_);
v___x_338_ = lean_array_push(v___x_337_, v_aSizeEqN_316_);
v___x_339_ = l_Lean_Meta_mkAppM(v___x_332_, v___x_338_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v_a_340_; lean_object* v___x_341_; lean_object* v___f_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v_a_340_ = lean_ctor_get(v___x_339_, 0);
lean_inc(v_a_340_);
lean_dec_ref_known(v___x_339_, 1);
v___x_341_ = lean_box(v___x_326_);
v___f_342_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed), 11, 5);
lean_closure_set(v___f_342_, 0, v_mvarId_312_);
lean_closure_set(v___f_342_, 1, v_xs_319_);
lean_closure_set(v___f_342_, 2, v___x_341_);
lean_closure_set(v___f_342_, 3, v_args_320_);
lean_closure_set(v___f_342_, 4, v_a_340_);
v___x_343_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3));
v___x_344_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_343_, v_a_331_, v___f_342_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_344_;
}
else
{
lean_object* v_a_345_; lean_object* v___x_347_; uint8_t v_isShared_348_; uint8_t v_isSharedCheck_352_; 
lean_dec(v_a_331_);
lean_dec_ref(v_args_320_);
lean_dec_ref(v_xs_319_);
lean_dec(v_mvarId_312_);
v_a_345_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_352_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_352_ == 0)
{
v___x_347_ = v___x_339_;
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
else
{
lean_inc(v_a_345_);
lean_dec(v___x_339_);
v___x_347_ = lean_box(0);
v_isShared_348_ = v_isSharedCheck_352_;
goto v_resetjp_346_;
}
v_resetjp_346_:
{
lean_object* v___x_350_; 
if (v_isShared_348_ == 0)
{
v___x_350_ = v___x_347_;
goto v_reusejp_349_;
}
else
{
lean_object* v_reuseFailAlloc_351_; 
v_reuseFailAlloc_351_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_351_, 0, v_a_345_);
v___x_350_ = v_reuseFailAlloc_351_;
goto v_reusejp_349_;
}
v_reusejp_349_:
{
return v___x_350_;
}
}
}
}
else
{
lean_object* v_a_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_360_; 
lean_dec_ref(v_args_320_);
lean_dec_ref(v_xs_319_);
lean_dec_ref(v_aSizeEqN_316_);
lean_dec(v_n_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_mvarId_312_);
v_a_353_ = lean_ctor_get(v___x_330_, 0);
v_isSharedCheck_360_ = !lean_is_exclusive(v___x_330_);
if (v_isSharedCheck_360_ == 0)
{
v___x_355_ = v___x_330_;
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_a_353_);
lean_dec(v___x_330_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_360_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_358_; 
if (v_isShared_356_ == 0)
{
v___x_358_ = v___x_355_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v_a_353_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
return v___x_358_;
}
}
}
}
else
{
lean_object* v_a_361_; lean_object* v___x_363_; uint8_t v_isShared_364_; uint8_t v_isSharedCheck_368_; 
lean_dec_ref(v_args_320_);
lean_dec_ref(v_xs_319_);
lean_dec_ref(v_aSizeEqN_316_);
lean_dec(v_n_314_);
lean_dec_ref(v_a_313_);
lean_dec(v_mvarId_312_);
v_a_361_ = lean_ctor_get(v___x_328_, 0);
v_isSharedCheck_368_ = !lean_is_exclusive(v___x_328_);
if (v_isSharedCheck_368_ == 0)
{
v___x_363_ = v___x_328_;
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
else
{
lean_inc(v_a_361_);
lean_dec(v___x_328_);
v___x_363_ = lean_box(0);
v_isShared_364_ = v_isSharedCheck_368_;
goto v_resetjp_362_;
}
v_resetjp_362_:
{
lean_object* v___x_366_; 
if (v_isShared_364_ == 0)
{
v___x_366_ = v___x_363_;
goto v_reusejp_365_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_a_361_);
v___x_366_ = v_reuseFailAlloc_367_;
goto v_reusejp_365_;
}
v_reusejp_365_:
{
return v___x_366_;
}
}
}
}
else
{
lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v___x_369_ = lean_unsigned_to_nat(1u);
v___x_370_ = lean_nat_add(v_i_318_, v___x_369_);
lean_inc(v___x_370_);
lean_inc_ref(v_00_u03b1_317_);
lean_inc(v_xNamePrefix_315_);
v___f_371_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed), 16, 10);
lean_closure_set(v___f_371_, 0, v_a_313_);
lean_closure_set(v___f_371_, 1, v_i_318_);
lean_closure_set(v___f_371_, 2, v_n_314_);
lean_closure_set(v___f_371_, 3, v_aSizeEqN_316_);
lean_closure_set(v___f_371_, 4, v_xs_319_);
lean_closure_set(v___f_371_, 5, v_args_320_);
lean_closure_set(v___f_371_, 6, v_mvarId_312_);
lean_closure_set(v___f_371_, 7, v_xNamePrefix_315_);
lean_closure_set(v___f_371_, 8, v_00_u03b1_317_);
lean_closure_set(v___f_371_, 9, v___x_370_);
v___x_372_ = lean_name_append_index_after(v_xNamePrefix_315_, v___x_370_);
v___x_373_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_372_, v_00_u03b1_317_, v___f_371_, v_a_321_, v_a_322_, v_a_323_, v_a_324_);
return v___x_373_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(lean_object* v_a_374_, lean_object* v_i_375_, lean_object* v_n_376_, lean_object* v_aSizeEqN_377_, lean_object* v_xs_378_, lean_object* v_args_379_, lean_object* v_mvarId_380_, lean_object* v_xNamePrefix_381_, lean_object* v_00_u03b1_382_, lean_object* v___x_383_, lean_object* v_xi_384_, lean_object* v___y_385_, lean_object* v___y_386_, lean_object* v___y_387_, lean_object* v___y_388_){
_start:
{
lean_object* v___x_390_; 
lean_inc_ref(v_aSizeEqN_377_);
lean_inc(v_n_376_);
lean_inc_ref(v_a_374_);
v___x_390_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_374_, v_i_375_, v_n_376_, v_aSizeEqN_377_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
if (lean_obj_tag(v___x_390_) == 0)
{
lean_object* v_a_391_; lean_object* v_xs_392_; lean_object* v___x_393_; lean_object* v___x_394_; 
v_a_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_a_391_);
lean_dec_ref_known(v___x_390_, 1);
v_xs_392_ = lean_array_push(v_xs_378_, v_xi_384_);
v___x_393_ = lean_array_push(v_args_379_, v_a_391_);
v___x_394_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_380_, v_a_374_, v_n_376_, v_xNamePrefix_381_, v_aSizeEqN_377_, v_00_u03b1_382_, v___x_383_, v_xs_392_, v___x_393_, v___y_385_, v___y_386_, v___y_387_, v___y_388_);
return v___x_394_;
}
else
{
lean_object* v_a_395_; lean_object* v___x_397_; uint8_t v_isShared_398_; uint8_t v_isSharedCheck_402_; 
lean_dec_ref(v_xi_384_);
lean_dec(v___x_383_);
lean_dec_ref(v_00_u03b1_382_);
lean_dec(v_xNamePrefix_381_);
lean_dec(v_mvarId_380_);
lean_dec_ref(v_args_379_);
lean_dec_ref(v_xs_378_);
lean_dec_ref(v_aSizeEqN_377_);
lean_dec(v_n_376_);
lean_dec_ref(v_a_374_);
v_a_395_ = lean_ctor_get(v___x_390_, 0);
v_isSharedCheck_402_ = !lean_is_exclusive(v___x_390_);
if (v_isSharedCheck_402_ == 0)
{
v___x_397_ = v___x_390_;
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
else
{
lean_inc(v_a_395_);
lean_dec(v___x_390_);
v___x_397_ = lean_box(0);
v_isShared_398_ = v_isSharedCheck_402_;
goto v_resetjp_396_;
}
v_resetjp_396_:
{
lean_object* v___x_400_; 
if (v_isShared_398_ == 0)
{
v___x_400_ = v___x_397_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_401_; 
v_reuseFailAlloc_401_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_401_, 0, v_a_395_);
v___x_400_ = v_reuseFailAlloc_401_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
return v___x_400_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___boxed(lean_object* v_mvarId_403_, lean_object* v_a_404_, lean_object* v_n_405_, lean_object* v_xNamePrefix_406_, lean_object* v_aSizeEqN_407_, lean_object* v_00_u03b1_408_, lean_object* v_i_409_, lean_object* v_xs_410_, lean_object* v_args_411_, lean_object* v_a_412_, lean_object* v_a_413_, lean_object* v_a_414_, lean_object* v_a_415_, lean_object* v_a_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_403_, v_a_404_, v_n_405_, v_xNamePrefix_406_, v_aSizeEqN_407_, v_00_u03b1_408_, v_i_409_, v_xs_410_, v_args_411_, v_a_412_, v_a_413_, v_a_414_, v_a_415_);
lean_dec(v_a_415_);
lean_dec_ref(v_a_414_);
lean_dec(v_a_413_);
lean_dec_ref(v_a_412_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(lean_object* v_00_u03b1_418_, lean_object* v_name_419_, uint8_t v_bi_420_, lean_object* v_type_421_, lean_object* v_k_422_, uint8_t v_kind_423_, lean_object* v___y_424_, lean_object* v___y_425_, lean_object* v___y_426_, lean_object* v___y_427_){
_start:
{
lean_object* v___x_429_; 
v___x_429_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_419_, v_bi_420_, v_type_421_, v_k_422_, v_kind_423_, v___y_424_, v___y_425_, v___y_426_, v___y_427_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_430_, lean_object* v_name_431_, lean_object* v_bi_432_, lean_object* v_type_433_, lean_object* v_k_434_, lean_object* v_kind_435_, lean_object* v___y_436_, lean_object* v___y_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_){
_start:
{
uint8_t v_bi_boxed_441_; uint8_t v_kind_boxed_442_; lean_object* v_res_443_; 
v_bi_boxed_441_ = lean_unbox(v_bi_432_);
v_kind_boxed_442_ = lean_unbox(v_kind_435_);
v_res_443_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(v_00_u03b1_430_, v_name_431_, v_bi_boxed_441_, v_type_433_, v_k_434_, v_kind_boxed_442_, v___y_436_, v___y_437_, v___y_438_, v___y_439_);
lean_dec(v___y_439_);
lean_dec_ref(v___y_438_);
lean_dec(v___y_437_);
lean_dec_ref(v___y_436_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(lean_object* v_00_u03b1_444_, lean_object* v_name_445_, lean_object* v_type_446_, lean_object* v_k_447_, lean_object* v___y_448_, lean_object* v___y_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_445_, v_type_446_, v_k_447_, v___y_448_, v___y_449_, v___y_450_, v___y_451_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___boxed(lean_object* v_00_u03b1_454_, lean_object* v_name_455_, lean_object* v_type_456_, lean_object* v_k_457_, lean_object* v___y_458_, lean_object* v___y_459_, lean_object* v___y_460_, lean_object* v___y_461_, lean_object* v___y_462_){
_start:
{
lean_object* v_res_463_; 
v_res_463_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(v_00_u03b1_454_, v_name_455_, v_type_456_, v_k_457_, v___y_458_, v___y_459_, v___y_460_, v___y_461_);
lean_dec(v___y_461_);
lean_dec_ref(v___y_460_);
lean_dec(v___y_459_);
lean_dec_ref(v___y_458_);
return v_res_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_464_, lean_object* v_x_465_, lean_object* v_x_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_ks_468_; lean_object* v_vs_469_; lean_object* v___x_471_; uint8_t v_isShared_472_; uint8_t v_isSharedCheck_493_; 
v_ks_468_ = lean_ctor_get(v_x_464_, 0);
v_vs_469_ = lean_ctor_get(v_x_464_, 1);
v_isSharedCheck_493_ = !lean_is_exclusive(v_x_464_);
if (v_isSharedCheck_493_ == 0)
{
v___x_471_ = v_x_464_;
v_isShared_472_ = v_isSharedCheck_493_;
goto v_resetjp_470_;
}
else
{
lean_inc(v_vs_469_);
lean_inc(v_ks_468_);
lean_dec(v_x_464_);
v___x_471_ = lean_box(0);
v_isShared_472_ = v_isSharedCheck_493_;
goto v_resetjp_470_;
}
v_resetjp_470_:
{
lean_object* v___x_473_; uint8_t v___x_474_; 
v___x_473_ = lean_array_get_size(v_ks_468_);
v___x_474_ = lean_nat_dec_lt(v_x_465_, v___x_473_);
if (v___x_474_ == 0)
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_478_; 
lean_dec(v_x_465_);
v___x_475_ = lean_array_push(v_ks_468_, v_x_466_);
v___x_476_ = lean_array_push(v_vs_469_, v_x_467_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_476_);
lean_ctor_set(v___x_471_, 0, v___x_475_);
v___x_478_ = v___x_471_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_475_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_476_);
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
lean_object* v_k_x27_480_; uint8_t v___x_481_; 
v_k_x27_480_ = lean_array_fget_borrowed(v_ks_468_, v_x_465_);
v___x_481_ = l_Lean_instBEqMVarId_beq(v_x_466_, v_k_x27_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_483_; 
if (v_isShared_472_ == 0)
{
v___x_483_ = v___x_471_;
goto v_reusejp_482_;
}
else
{
lean_object* v_reuseFailAlloc_487_; 
v_reuseFailAlloc_487_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_487_, 0, v_ks_468_);
lean_ctor_set(v_reuseFailAlloc_487_, 1, v_vs_469_);
v___x_483_ = v_reuseFailAlloc_487_;
goto v_reusejp_482_;
}
v_reusejp_482_:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_x_465_, v___x_484_);
lean_dec(v_x_465_);
v_x_464_ = v___x_483_;
v_x_465_ = v___x_485_;
goto _start;
}
}
else
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_491_; 
v___x_488_ = lean_array_fset(v_ks_468_, v_x_465_, v_x_466_);
v___x_489_ = lean_array_fset(v_vs_469_, v_x_465_, v_x_467_);
lean_dec(v_x_465_);
if (v_isShared_472_ == 0)
{
lean_ctor_set(v___x_471_, 1, v___x_489_);
lean_ctor_set(v___x_471_, 0, v___x_488_);
v___x_491_ = v___x_471_;
goto v_reusejp_490_;
}
else
{
lean_object* v_reuseFailAlloc_492_; 
v_reuseFailAlloc_492_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_492_, 0, v___x_488_);
lean_ctor_set(v_reuseFailAlloc_492_, 1, v___x_489_);
v___x_491_ = v_reuseFailAlloc_492_;
goto v_reusejp_490_;
}
v_reusejp_490_:
{
return v___x_491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_494_, lean_object* v_k_495_, lean_object* v_v_496_){
_start:
{
lean_object* v___x_497_; lean_object* v___x_498_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v___x_498_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_494_, v___x_497_, v_k_495_, v_v_496_);
return v___x_498_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_499_; 
v___x_499_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_499_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(lean_object* v_x_500_, size_t v_x_501_, size_t v_x_502_, lean_object* v_x_503_, lean_object* v_x_504_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v_es_505_; size_t v___x_506_; size_t v___x_507_; lean_object* v_j_508_; lean_object* v___x_509_; uint8_t v___x_510_; 
v_es_505_ = lean_ctor_get(v_x_500_, 0);
v___x_506_ = ((size_t)31ULL);
v___x_507_ = lean_usize_land(v_x_501_, v___x_506_);
v_j_508_ = lean_usize_to_nat(v___x_507_);
v___x_509_ = lean_array_get_size(v_es_505_);
v___x_510_ = lean_nat_dec_lt(v_j_508_, v___x_509_);
if (v___x_510_ == 0)
{
lean_dec(v_j_508_);
lean_dec(v_x_504_);
lean_dec(v_x_503_);
return v_x_500_;
}
else
{
lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_549_; 
lean_inc_ref(v_es_505_);
v_isSharedCheck_549_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v_x_500_, 0);
lean_dec(v_unused_550_);
v___x_512_ = v_x_500_;
v_isShared_513_ = v_isSharedCheck_549_;
goto v_resetjp_511_;
}
else
{
lean_dec(v_x_500_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_549_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v_v_514_; lean_object* v___x_515_; lean_object* v_xs_x27_516_; lean_object* v___y_518_; 
v_v_514_ = lean_array_fget(v_es_505_, v_j_508_);
v___x_515_ = lean_box(0);
v_xs_x27_516_ = lean_array_fset(v_es_505_, v_j_508_, v___x_515_);
switch(lean_obj_tag(v_v_514_))
{
case 0:
{
lean_object* v_key_523_; lean_object* v_val_524_; lean_object* v___x_526_; uint8_t v_isShared_527_; uint8_t v_isSharedCheck_534_; 
v_key_523_ = lean_ctor_get(v_v_514_, 0);
v_val_524_ = lean_ctor_get(v_v_514_, 1);
v_isSharedCheck_534_ = !lean_is_exclusive(v_v_514_);
if (v_isSharedCheck_534_ == 0)
{
v___x_526_ = v_v_514_;
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
else
{
lean_inc(v_val_524_);
lean_inc(v_key_523_);
lean_dec(v_v_514_);
v___x_526_ = lean_box(0);
v_isShared_527_ = v_isSharedCheck_534_;
goto v_resetjp_525_;
}
v_resetjp_525_:
{
uint8_t v___x_528_; 
v___x_528_ = l_Lean_instBEqMVarId_beq(v_x_503_, v_key_523_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_del_object(v___x_526_);
v___x_529_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_523_, v_val_524_, v_x_503_, v_x_504_);
v___x_530_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_530_, 0, v___x_529_);
v___y_518_ = v___x_530_;
goto v___jp_517_;
}
else
{
lean_object* v___x_532_; 
lean_dec(v_val_524_);
lean_dec(v_key_523_);
if (v_isShared_527_ == 0)
{
lean_ctor_set(v___x_526_, 1, v_x_504_);
lean_ctor_set(v___x_526_, 0, v_x_503_);
v___x_532_ = v___x_526_;
goto v_reusejp_531_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_x_503_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_x_504_);
v___x_532_ = v_reuseFailAlloc_533_;
goto v_reusejp_531_;
}
v_reusejp_531_:
{
v___y_518_ = v___x_532_;
goto v___jp_517_;
}
}
}
}
case 1:
{
lean_object* v_node_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_547_; 
v_node_535_ = lean_ctor_get(v_v_514_, 0);
v_isSharedCheck_547_ = !lean_is_exclusive(v_v_514_);
if (v_isSharedCheck_547_ == 0)
{
v___x_537_ = v_v_514_;
v_isShared_538_ = v_isSharedCheck_547_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_node_535_);
lean_dec(v_v_514_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_547_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
size_t v___x_539_; size_t v___x_540_; size_t v___x_541_; size_t v___x_542_; lean_object* v___x_543_; lean_object* v___x_545_; 
v___x_539_ = ((size_t)5ULL);
v___x_540_ = lean_usize_shift_right(v_x_501_, v___x_539_);
v___x_541_ = ((size_t)1ULL);
v___x_542_ = lean_usize_add(v_x_502_, v___x_541_);
v___x_543_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_node_535_, v___x_540_, v___x_542_, v_x_503_, v_x_504_);
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 0, v___x_543_);
v___x_545_ = v___x_537_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_543_);
v___x_545_ = v_reuseFailAlloc_546_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
v___y_518_ = v___x_545_;
goto v___jp_517_;
}
}
}
default: 
{
lean_object* v___x_548_; 
v___x_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_548_, 0, v_x_503_);
lean_ctor_set(v___x_548_, 1, v_x_504_);
v___y_518_ = v___x_548_;
goto v___jp_517_;
}
}
v___jp_517_:
{
lean_object* v___x_519_; lean_object* v___x_521_; 
v___x_519_ = lean_array_fset(v_xs_x27_516_, v_j_508_, v___y_518_);
lean_dec(v_j_508_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 0, v___x_519_);
v___x_521_ = v___x_512_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_522_; 
v_reuseFailAlloc_522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_522_, 0, v___x_519_);
v___x_521_ = v_reuseFailAlloc_522_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
return v___x_521_;
}
}
}
}
}
else
{
lean_object* v_ks_551_; lean_object* v_vs_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_572_; 
v_ks_551_ = lean_ctor_get(v_x_500_, 0);
v_vs_552_ = lean_ctor_get(v_x_500_, 1);
v_isSharedCheck_572_ = !lean_is_exclusive(v_x_500_);
if (v_isSharedCheck_572_ == 0)
{
v___x_554_ = v_x_500_;
v_isShared_555_ = v_isSharedCheck_572_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_vs_552_);
lean_inc(v_ks_551_);
lean_dec(v_x_500_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_572_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_557_; 
if (v_isShared_555_ == 0)
{
v___x_557_ = v___x_554_;
goto v_reusejp_556_;
}
else
{
lean_object* v_reuseFailAlloc_571_; 
v_reuseFailAlloc_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_571_, 0, v_ks_551_);
lean_ctor_set(v_reuseFailAlloc_571_, 1, v_vs_552_);
v___x_557_ = v_reuseFailAlloc_571_;
goto v_reusejp_556_;
}
v_reusejp_556_:
{
lean_object* v_newNode_558_; uint8_t v___y_560_; size_t v___x_566_; uint8_t v___x_567_; 
v_newNode_558_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v___x_557_, v_x_503_, v_x_504_);
v___x_566_ = ((size_t)7ULL);
v___x_567_ = lean_usize_dec_le(v___x_566_, v_x_502_);
if (v___x_567_ == 0)
{
lean_object* v___x_568_; lean_object* v___x_569_; uint8_t v___x_570_; 
v___x_568_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_558_);
v___x_569_ = lean_unsigned_to_nat(4u);
v___x_570_ = lean_nat_dec_lt(v___x_568_, v___x_569_);
lean_dec(v___x_568_);
v___y_560_ = v___x_570_;
goto v___jp_559_;
}
else
{
v___y_560_ = v___x_567_;
goto v___jp_559_;
}
v___jp_559_:
{
if (v___y_560_ == 0)
{
lean_object* v_ks_561_; lean_object* v_vs_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; 
v_ks_561_ = lean_ctor_get(v_newNode_558_, 0);
lean_inc_ref(v_ks_561_);
v_vs_562_ = lean_ctor_get(v_newNode_558_, 1);
lean_inc_ref(v_vs_562_);
lean_dec_ref(v_newNode_558_);
v___x_563_ = lean_unsigned_to_nat(0u);
v___x_564_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_565_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_x_502_, v_ks_561_, v_vs_562_, v___x_563_, v___x_564_);
lean_dec_ref(v_vs_562_);
lean_dec_ref(v_ks_561_);
return v___x_565_;
}
else
{
return v_newNode_558_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_573_, lean_object* v_keys_574_, lean_object* v_vals_575_, lean_object* v_i_576_, lean_object* v_entries_577_){
_start:
{
lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_578_ = lean_array_get_size(v_keys_574_);
v___x_579_ = lean_nat_dec_lt(v_i_576_, v___x_578_);
if (v___x_579_ == 0)
{
lean_dec(v_i_576_);
return v_entries_577_;
}
else
{
lean_object* v_k_580_; lean_object* v_v_581_; uint64_t v___x_582_; size_t v_h_583_; size_t v___x_584_; lean_object* v___x_585_; size_t v___x_586_; size_t v___x_587_; size_t v___x_588_; size_t v_h_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v_k_580_ = lean_array_fget_borrowed(v_keys_574_, v_i_576_);
v_v_581_ = lean_array_fget_borrowed(v_vals_575_, v_i_576_);
v___x_582_ = l_Lean_instHashableMVarId_hash(v_k_580_);
v_h_583_ = lean_uint64_to_usize(v___x_582_);
v___x_584_ = ((size_t)5ULL);
v___x_585_ = lean_unsigned_to_nat(1u);
v___x_586_ = ((size_t)1ULL);
v___x_587_ = lean_usize_sub(v_depth_573_, v___x_586_);
v___x_588_ = lean_usize_mul(v___x_584_, v___x_587_);
v_h_589_ = lean_usize_shift_right(v_h_583_, v___x_588_);
v___x_590_ = lean_nat_add(v_i_576_, v___x_585_);
lean_dec(v_i_576_);
lean_inc(v_v_581_);
lean_inc(v_k_580_);
v___x_591_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_entries_577_, v_h_589_, v_depth_573_, v_k_580_, v_v_581_);
v_i_576_ = v___x_590_;
v_entries_577_ = v___x_591_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_593_, lean_object* v_keys_594_, lean_object* v_vals_595_, lean_object* v_i_596_, lean_object* v_entries_597_){
_start:
{
size_t v_depth_boxed_598_; lean_object* v_res_599_; 
v_depth_boxed_598_ = lean_unbox_usize(v_depth_593_);
lean_dec(v_depth_593_);
v_res_599_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_598_, v_keys_594_, v_vals_595_, v_i_596_, v_entries_597_);
lean_dec_ref(v_vals_595_);
lean_dec_ref(v_keys_594_);
return v_res_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_600_, lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_){
_start:
{
size_t v_x_988__boxed_605_; size_t v_x_989__boxed_606_; lean_object* v_res_607_; 
v_x_988__boxed_605_ = lean_unbox_usize(v_x_601_);
lean_dec(v_x_601_);
v_x_989__boxed_606_ = lean_unbox_usize(v_x_602_);
lean_dec(v_x_602_);
v_res_607_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_600_, v_x_988__boxed_605_, v_x_989__boxed_606_, v_x_603_, v_x_604_);
return v_res_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(lean_object* v_x_608_, lean_object* v_x_609_, lean_object* v_x_610_){
_start:
{
uint64_t v___x_611_; size_t v___x_612_; size_t v___x_613_; lean_object* v___x_614_; 
v___x_611_ = l_Lean_instHashableMVarId_hash(v_x_609_);
v___x_612_ = lean_uint64_to_usize(v___x_611_);
v___x_613_ = ((size_t)1ULL);
v___x_614_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_608_, v___x_612_, v___x_613_, v_x_609_, v_x_610_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(lean_object* v_mvarId_615_, lean_object* v_val_616_, lean_object* v___y_617_){
_start:
{
lean_object* v___x_619_; lean_object* v_mctx_620_; lean_object* v_cache_621_; lean_object* v_zetaDeltaFVarIds_622_; lean_object* v_postponed_623_; lean_object* v_diag_624_; lean_object* v___x_626_; uint8_t v_isShared_627_; uint8_t v_isSharedCheck_653_; 
v___x_619_ = lean_st_ref_take(v___y_617_);
v_mctx_620_ = lean_ctor_get(v___x_619_, 0);
v_cache_621_ = lean_ctor_get(v___x_619_, 1);
v_zetaDeltaFVarIds_622_ = lean_ctor_get(v___x_619_, 2);
v_postponed_623_ = lean_ctor_get(v___x_619_, 3);
v_diag_624_ = lean_ctor_get(v___x_619_, 4);
v_isSharedCheck_653_ = !lean_is_exclusive(v___x_619_);
if (v_isSharedCheck_653_ == 0)
{
v___x_626_ = v___x_619_;
v_isShared_627_ = v_isSharedCheck_653_;
goto v_resetjp_625_;
}
else
{
lean_inc(v_diag_624_);
lean_inc(v_postponed_623_);
lean_inc(v_zetaDeltaFVarIds_622_);
lean_inc(v_cache_621_);
lean_inc(v_mctx_620_);
lean_dec(v___x_619_);
v___x_626_ = lean_box(0);
v_isShared_627_ = v_isSharedCheck_653_;
goto v_resetjp_625_;
}
v_resetjp_625_:
{
lean_object* v_depth_628_; lean_object* v_levelAssignDepth_629_; lean_object* v_lmvarCounter_630_; lean_object* v_mvarCounter_631_; lean_object* v_lDecls_632_; lean_object* v_decls_633_; lean_object* v_userNames_634_; lean_object* v_lAssignment_635_; lean_object* v_eAssignment_636_; lean_object* v_dAssignment_637_; lean_object* v_instanceTypedMVars_638_; lean_object* v___x_640_; uint8_t v_isShared_641_; uint8_t v_isSharedCheck_652_; 
v_depth_628_ = lean_ctor_get(v_mctx_620_, 0);
v_levelAssignDepth_629_ = lean_ctor_get(v_mctx_620_, 1);
v_lmvarCounter_630_ = lean_ctor_get(v_mctx_620_, 2);
v_mvarCounter_631_ = lean_ctor_get(v_mctx_620_, 3);
v_lDecls_632_ = lean_ctor_get(v_mctx_620_, 4);
v_decls_633_ = lean_ctor_get(v_mctx_620_, 5);
v_userNames_634_ = lean_ctor_get(v_mctx_620_, 6);
v_lAssignment_635_ = lean_ctor_get(v_mctx_620_, 7);
v_eAssignment_636_ = lean_ctor_get(v_mctx_620_, 8);
v_dAssignment_637_ = lean_ctor_get(v_mctx_620_, 9);
v_instanceTypedMVars_638_ = lean_ctor_get(v_mctx_620_, 10);
v_isSharedCheck_652_ = !lean_is_exclusive(v_mctx_620_);
if (v_isSharedCheck_652_ == 0)
{
v___x_640_ = v_mctx_620_;
v_isShared_641_ = v_isSharedCheck_652_;
goto v_resetjp_639_;
}
else
{
lean_inc(v_instanceTypedMVars_638_);
lean_inc(v_dAssignment_637_);
lean_inc(v_eAssignment_636_);
lean_inc(v_lAssignment_635_);
lean_inc(v_userNames_634_);
lean_inc(v_decls_633_);
lean_inc(v_lDecls_632_);
lean_inc(v_mvarCounter_631_);
lean_inc(v_lmvarCounter_630_);
lean_inc(v_levelAssignDepth_629_);
lean_inc(v_depth_628_);
lean_dec(v_mctx_620_);
v___x_640_ = lean_box(0);
v_isShared_641_ = v_isSharedCheck_652_;
goto v_resetjp_639_;
}
v_resetjp_639_:
{
lean_object* v___x_642_; lean_object* v___x_644_; 
v___x_642_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_eAssignment_636_, v_mvarId_615_, v_val_616_);
if (v_isShared_641_ == 0)
{
lean_ctor_set(v___x_640_, 8, v___x_642_);
v___x_644_ = v___x_640_;
goto v_reusejp_643_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_depth_628_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_levelAssignDepth_629_);
lean_ctor_set(v_reuseFailAlloc_651_, 2, v_lmvarCounter_630_);
lean_ctor_set(v_reuseFailAlloc_651_, 3, v_mvarCounter_631_);
lean_ctor_set(v_reuseFailAlloc_651_, 4, v_lDecls_632_);
lean_ctor_set(v_reuseFailAlloc_651_, 5, v_decls_633_);
lean_ctor_set(v_reuseFailAlloc_651_, 6, v_userNames_634_);
lean_ctor_set(v_reuseFailAlloc_651_, 7, v_lAssignment_635_);
lean_ctor_set(v_reuseFailAlloc_651_, 8, v___x_642_);
lean_ctor_set(v_reuseFailAlloc_651_, 9, v_dAssignment_637_);
lean_ctor_set(v_reuseFailAlloc_651_, 10, v_instanceTypedMVars_638_);
v___x_644_ = v_reuseFailAlloc_651_;
goto v_reusejp_643_;
}
v_reusejp_643_:
{
lean_object* v___x_646_; 
if (v_isShared_627_ == 0)
{
lean_ctor_set(v___x_626_, 0, v___x_644_);
v___x_646_ = v___x_626_;
goto v_reusejp_645_;
}
else
{
lean_object* v_reuseFailAlloc_650_; 
v_reuseFailAlloc_650_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_650_, 0, v___x_644_);
lean_ctor_set(v_reuseFailAlloc_650_, 1, v_cache_621_);
lean_ctor_set(v_reuseFailAlloc_650_, 2, v_zetaDeltaFVarIds_622_);
lean_ctor_set(v_reuseFailAlloc_650_, 3, v_postponed_623_);
lean_ctor_set(v_reuseFailAlloc_650_, 4, v_diag_624_);
v___x_646_ = v_reuseFailAlloc_650_;
goto v_reusejp_645_;
}
v_reusejp_645_:
{
lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; 
v___x_647_ = lean_st_ref_put(v___y_617_, v___x_646_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
return v___x_649_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg___boxed(lean_object* v_mvarId_654_, lean_object* v_val_655_, lean_object* v___y_656_, lean_object* v___y_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_654_, v_val_655_, v___y_656_);
lean_dec(v___y_656_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object* v_mvarId_661_, lean_object* v_a_662_, lean_object* v_n_663_, lean_object* v_xNamePrefix_664_, lean_object* v_aSizeEqN_665_, lean_object* v_a_666_, lean_object* v_a_667_, lean_object* v_a_668_, lean_object* v_a_669_){
_start:
{
lean_object* v___x_671_; 
lean_inc_ref(v_a_662_);
v___x_671_ = l_Lean_Meta_getArrayArgType(v_a_662_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_671_) == 0)
{
lean_object* v_a_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; 
v_a_672_ = lean_ctor_get(v___x_671_, 0);
lean_inc(v_a_672_);
lean_dec_ref_known(v___x_671_, 1);
v___x_673_ = lean_unsigned_to_nat(0u);
v___x_674_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0));
lean_inc(v_mvarId_661_);
v___x_675_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_661_, v_a_662_, v_n_663_, v_xNamePrefix_664_, v_aSizeEqN_665_, v_a_672_, v___x_673_, v___x_674_, v___x_674_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_675_) == 0)
{
lean_object* v_a_676_; lean_object* v_fst_677_; lean_object* v_snd_678_; lean_object* v___x_679_; 
v_a_676_ = lean_ctor_get(v___x_675_, 0);
lean_inc(v_a_676_);
lean_dec_ref_known(v___x_675_, 1);
v_fst_677_ = lean_ctor_get(v_a_676_, 0);
lean_inc(v_fst_677_);
v_snd_678_ = lean_ctor_get(v_a_676_, 1);
lean_inc(v_snd_678_);
lean_dec(v_a_676_);
lean_inc(v_mvarId_661_);
v___x_679_ = l_Lean_MVarId_getTag(v_mvarId_661_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_679_) == 0)
{
lean_object* v_a_680_; lean_object* v___x_681_; 
v_a_680_ = lean_ctor_get(v___x_679_, 0);
lean_inc(v_a_680_);
lean_dec_ref_known(v___x_679_, 1);
v___x_681_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_677_, v_a_680_, v_a_666_, v_a_667_, v_a_668_, v_a_669_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc_n(v_a_682_, 2);
lean_dec_ref_known(v___x_681_, 1);
v___x_683_ = l_Lean_mkAppN(v_a_682_, v_snd_678_);
lean_dec(v_snd_678_);
v___x_684_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_661_, v___x_683_, v_a_667_);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_684_);
if (v_isSharedCheck_692_ == 0)
{
lean_object* v_unused_693_; 
v_unused_693_ = lean_ctor_get(v___x_684_, 0);
lean_dec(v_unused_693_);
v___x_686_ = v___x_684_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_dec(v___x_684_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = l_Lean_Expr_mvarId_x21(v_a_682_);
lean_dec(v_a_682_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
return v___x_690_;
}
}
}
else
{
lean_object* v_a_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_701_; 
lean_dec(v_snd_678_);
lean_dec(v_mvarId_661_);
v_a_694_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_701_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_701_ == 0)
{
v___x_696_ = v___x_681_;
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_a_694_);
lean_dec(v___x_681_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_701_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_699_; 
if (v_isShared_697_ == 0)
{
v___x_699_ = v___x_696_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v_a_694_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
else
{
lean_object* v_a_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_709_; 
lean_dec(v_snd_678_);
lean_dec(v_fst_677_);
lean_dec(v_mvarId_661_);
v_a_702_ = lean_ctor_get(v___x_679_, 0);
v_isSharedCheck_709_ = !lean_is_exclusive(v___x_679_);
if (v_isSharedCheck_709_ == 0)
{
v___x_704_ = v___x_679_;
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
else
{
lean_inc(v_a_702_);
lean_dec(v___x_679_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_709_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_707_; 
if (v_isShared_705_ == 0)
{
v___x_707_ = v___x_704_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_a_702_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
return v___x_707_;
}
}
}
}
else
{
lean_object* v_a_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_717_; 
lean_dec(v_mvarId_661_);
v_a_710_ = lean_ctor_get(v___x_675_, 0);
v_isSharedCheck_717_ = !lean_is_exclusive(v___x_675_);
if (v_isSharedCheck_717_ == 0)
{
v___x_712_ = v___x_675_;
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_a_710_);
lean_dec(v___x_675_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_717_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
lean_object* v___x_715_; 
if (v_isShared_713_ == 0)
{
v___x_715_ = v___x_712_;
goto v_reusejp_714_;
}
else
{
lean_object* v_reuseFailAlloc_716_; 
v_reuseFailAlloc_716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_716_, 0, v_a_710_);
v___x_715_ = v_reuseFailAlloc_716_;
goto v_reusejp_714_;
}
v_reusejp_714_:
{
return v___x_715_;
}
}
}
}
else
{
lean_object* v_a_718_; lean_object* v___x_720_; uint8_t v_isShared_721_; uint8_t v_isSharedCheck_725_; 
lean_dec_ref(v_aSizeEqN_665_);
lean_dec(v_xNamePrefix_664_);
lean_dec(v_n_663_);
lean_dec_ref(v_a_662_);
lean_dec(v_mvarId_661_);
v_a_718_ = lean_ctor_get(v___x_671_, 0);
v_isSharedCheck_725_ = !lean_is_exclusive(v___x_671_);
if (v_isSharedCheck_725_ == 0)
{
v___x_720_ = v___x_671_;
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
else
{
lean_inc(v_a_718_);
lean_dec(v___x_671_);
v___x_720_ = lean_box(0);
v_isShared_721_ = v_isSharedCheck_725_;
goto v_resetjp_719_;
}
v_resetjp_719_:
{
lean_object* v___x_723_; 
if (v_isShared_721_ == 0)
{
v___x_723_ = v___x_720_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_a_718_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
return v___x_723_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___boxed(lean_object* v_mvarId_726_, lean_object* v_a_727_, lean_object* v_n_728_, lean_object* v_xNamePrefix_729_, lean_object* v_aSizeEqN_730_, lean_object* v_a_731_, lean_object* v_a_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_726_, v_a_727_, v_n_728_, v_xNamePrefix_729_, v_aSizeEqN_730_, v_a_731_, v_a_732_, v_a_733_, v_a_734_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
lean_dec(v_a_732_);
lean_dec_ref(v_a_731_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(lean_object* v_mvarId_737_, lean_object* v_val_738_, lean_object* v___y_739_, lean_object* v___y_740_, lean_object* v___y_741_, lean_object* v___y_742_){
_start:
{
lean_object* v___x_744_; 
v___x_744_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_737_, v_val_738_, v___y_740_);
return v___x_744_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___boxed(lean_object* v_mvarId_745_, lean_object* v_val_746_, lean_object* v___y_747_, lean_object* v___y_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_){
_start:
{
lean_object* v_res_752_; 
v_res_752_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(v_mvarId_745_, v_val_746_, v___y_747_, v___y_748_, v___y_749_, v___y_750_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
lean_dec(v___y_748_);
lean_dec_ref(v___y_747_);
return v_res_752_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0(lean_object* v_00_u03b2_753_, lean_object* v_x_754_, lean_object* v_x_755_, lean_object* v_x_756_){
_start:
{
lean_object* v___x_757_; 
v___x_757_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_x_754_, v_x_755_, v_x_756_);
return v___x_757_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_758_, lean_object* v_x_759_, size_t v_x_760_, size_t v_x_761_, lean_object* v_x_762_, lean_object* v_x_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_759_, v_x_760_, v_x_761_, v_x_762_, v_x_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_765_, lean_object* v_x_766_, lean_object* v_x_767_, lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_){
_start:
{
size_t v_x_1348__boxed_771_; size_t v_x_1349__boxed_772_; lean_object* v_res_773_; 
v_x_1348__boxed_771_ = lean_unbox_usize(v_x_767_);
lean_dec(v_x_767_);
v_x_1349__boxed_772_ = lean_unbox_usize(v_x_768_);
lean_dec(v_x_768_);
v_res_773_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(v_00_u03b2_765_, v_x_766_, v_x_1348__boxed_771_, v_x_1349__boxed_772_, v_x_769_, v_x_770_);
return v_res_773_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_774_, lean_object* v_n_775_, lean_object* v_k_776_, lean_object* v_v_777_){
_start:
{
lean_object* v___x_778_; 
v___x_778_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v_n_775_, v_k_776_, v_v_777_);
return v___x_778_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_779_, size_t v_depth_780_, lean_object* v_keys_781_, lean_object* v_vals_782_, lean_object* v_heq_783_, lean_object* v_i_784_, lean_object* v_entries_785_){
_start:
{
lean_object* v___x_786_; 
v___x_786_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_780_, v_keys_781_, v_vals_782_, v_i_784_, v_entries_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_787_, lean_object* v_depth_788_, lean_object* v_keys_789_, lean_object* v_vals_790_, lean_object* v_heq_791_, lean_object* v_i_792_, lean_object* v_entries_793_){
_start:
{
size_t v_depth_boxed_794_; lean_object* v_res_795_; 
v_depth_boxed_794_ = lean_unbox_usize(v_depth_788_);
lean_dec(v_depth_788_);
v_res_795_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_787_, v_depth_boxed_794_, v_keys_789_, v_vals_790_, v_heq_791_, v_i_792_, v_entries_793_);
lean_dec_ref(v_vals_790_);
lean_dec_ref(v_keys_789_);
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_796_, lean_object* v_x_797_, lean_object* v_x_798_, lean_object* v_x_799_, lean_object* v_x_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_797_, v_x_798_, v_x_799_, v_x_800_);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(lean_object* v_mvarId_802_, lean_object* v_x_803_, lean_object* v___y_804_, lean_object* v___y_805_, lean_object* v___y_806_, lean_object* v___y_807_){
_start:
{
lean_object* v___x_809_; 
v___x_809_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_802_, v_x_803_, v___y_804_, v___y_805_, v___y_806_, v___y_807_);
if (lean_obj_tag(v___x_809_) == 0)
{
lean_object* v_a_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_817_; 
v_a_810_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_817_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_817_ == 0)
{
v___x_812_ = v___x_809_;
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_a_810_);
lean_dec(v___x_809_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_817_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_815_; 
if (v_isShared_813_ == 0)
{
v___x_815_ = v___x_812_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v_a_810_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
else
{
lean_object* v_a_818_; lean_object* v___x_820_; uint8_t v_isShared_821_; uint8_t v_isSharedCheck_825_; 
v_a_818_ = lean_ctor_get(v___x_809_, 0);
v_isSharedCheck_825_ = !lean_is_exclusive(v___x_809_);
if (v_isSharedCheck_825_ == 0)
{
v___x_820_ = v___x_809_;
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
else
{
lean_inc(v_a_818_);
lean_dec(v___x_809_);
v___x_820_ = lean_box(0);
v_isShared_821_ = v_isSharedCheck_825_;
goto v_resetjp_819_;
}
v_resetjp_819_:
{
lean_object* v___x_823_; 
if (v_isShared_821_ == 0)
{
v___x_823_ = v___x_820_;
goto v_reusejp_822_;
}
else
{
lean_object* v_reuseFailAlloc_824_; 
v_reuseFailAlloc_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_824_, 0, v_a_818_);
v___x_823_ = v_reuseFailAlloc_824_;
goto v_reusejp_822_;
}
v_reusejp_822_:
{
return v___x_823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg___boxed(lean_object* v_mvarId_826_, lean_object* v_x_827_, lean_object* v___y_828_, lean_object* v___y_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_826_, v_x_827_, v___y_828_, v___y_829_, v___y_830_, v___y_831_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
lean_dec(v___y_829_);
lean_dec_ref(v___y_828_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(lean_object* v_00_u03b1_834_, lean_object* v_mvarId_835_, lean_object* v_x_836_, lean_object* v___y_837_, lean_object* v___y_838_, lean_object* v___y_839_, lean_object* v___y_840_){
_start:
{
lean_object* v___x_842_; 
v___x_842_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_835_, v_x_836_, v___y_837_, v___y_838_, v___y_839_, v___y_840_);
return v___x_842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___boxed(lean_object* v_00_u03b1_843_, lean_object* v_mvarId_844_, lean_object* v_x_845_, lean_object* v___y_846_, lean_object* v___y_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(v_00_u03b1_843_, v_mvarId_844_, v_x_845_, v___y_846_, v___y_847_, v___y_848_, v___y_849_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
lean_dec(v___y_847_);
lean_dec_ref(v___y_846_);
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(size_t v_sz_852_, size_t v_i_853_, lean_object* v_bs_854_){
_start:
{
uint8_t v___x_855_; 
v___x_855_ = lean_usize_dec_lt(v_i_853_, v_sz_852_);
if (v___x_855_ == 0)
{
return v_bs_854_;
}
else
{
lean_object* v_v_856_; lean_object* v___x_857_; lean_object* v_bs_x27_858_; lean_object* v___x_859_; size_t v___x_860_; size_t v___x_861_; lean_object* v___x_862_; 
v_v_856_ = lean_array_uget(v_bs_854_, v_i_853_);
v___x_857_ = lean_unsigned_to_nat(0u);
v_bs_x27_858_ = lean_array_uset(v_bs_854_, v_i_853_, v___x_857_);
v___x_859_ = l_Lean_mkRawNatLit(v_v_856_);
v___x_860_ = ((size_t)1ULL);
v___x_861_ = lean_usize_add(v_i_853_, v___x_860_);
v___x_862_ = lean_array_uset(v_bs_x27_858_, v_i_853_, v___x_859_);
v_i_853_ = v___x_861_;
v_bs_854_ = v___x_862_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0___boxed(lean_object* v_sz_864_, lean_object* v_i_865_, lean_object* v_bs_866_){
_start:
{
size_t v_sz_boxed_867_; size_t v_i_boxed_868_; lean_object* v_res_869_; 
v_sz_boxed_867_ = lean_unbox_usize(v_sz_864_);
lean_dec(v_sz_864_);
v_i_boxed_868_ = lean_unbox_usize(v_i_865_);
lean_dec(v_i_865_);
v_res_869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_boxed_867_, v_i_boxed_868_, v_bs_866_);
return v_res_869_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(lean_object* v___x_870_, lean_object* v_mvarId_871_, lean_object* v_a_872_, lean_object* v___x_873_, lean_object* v_xNamePrefix_874_, lean_object* v___x_875_, lean_object* v_subst_876_, uint8_t v___x_877_, lean_object* v___y_878_, lean_object* v___y_879_, lean_object* v___y_880_, lean_object* v___y_881_){
_start:
{
lean_object* v___x_883_; 
v___x_883_ = l_Lean_Meta_mkEqSymm(v___x_870_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_883_) == 0)
{
lean_object* v_a_884_; lean_object* v___x_885_; 
v_a_884_ = lean_ctor_get(v___x_883_, 0);
lean_inc(v_a_884_);
lean_dec_ref_known(v___x_883_, 1);
lean_inc(v___x_873_);
v___x_885_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_871_, v_a_872_, v___x_873_, v_xNamePrefix_874_, v_a_884_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; uint8_t v___x_888_; lean_object* v___x_889_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
v___x_887_ = lean_box(0);
v___x_888_ = 0;
v___x_889_ = l_Lean_Meta_introNCore(v_a_886_, v___x_873_, v___x_887_, v___x_888_, v___x_888_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_889_) == 0)
{
lean_object* v_a_890_; lean_object* v_fst_891_; lean_object* v_snd_892_; lean_object* v___x_893_; 
v_a_890_ = lean_ctor_get(v___x_889_, 0);
lean_inc(v_a_890_);
lean_dec_ref_known(v___x_889_, 1);
v_fst_891_ = lean_ctor_get(v_a_890_, 0);
lean_inc(v_fst_891_);
v_snd_892_ = lean_ctor_get(v_a_890_, 1);
lean_inc(v_snd_892_);
lean_dec(v_a_890_);
v___x_893_ = l_Lean_Meta_intro1Core(v_snd_892_, v___x_888_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_893_) == 0)
{
lean_object* v_a_894_; lean_object* v_fst_895_; lean_object* v_snd_896_; lean_object* v___x_897_; 
v_a_894_ = lean_ctor_get(v___x_893_, 0);
lean_inc(v_a_894_);
lean_dec_ref_known(v___x_893_, 1);
v_fst_895_ = lean_ctor_get(v_a_894_, 0);
lean_inc(v_fst_895_);
v_snd_896_ = lean_ctor_get(v_a_894_, 1);
lean_inc(v_snd_896_);
lean_dec(v_a_894_);
v___x_897_ = l_Lean_MVarId_clear(v_snd_896_, v___x_875_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v_a_898_; lean_object* v___x_899_; 
v_a_898_ = lean_ctor_get(v___x_897_, 0);
lean_inc(v_a_898_);
lean_dec_ref_known(v___x_897_, 1);
v___x_899_ = l_Lean_Meta_substCore(v_a_898_, v_fst_895_, v___x_888_, v_subst_876_, v___x_877_, v___x_888_, v___y_878_, v___y_879_, v___y_880_, v___y_881_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_902_; uint8_t v_isShared_903_; uint8_t v_isSharedCheck_911_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_911_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_911_ == 0)
{
v___x_902_ = v___x_899_;
v_isShared_903_ = v_isSharedCheck_911_;
goto v_resetjp_901_;
}
else
{
lean_inc(v_a_900_);
lean_dec(v___x_899_);
v___x_902_ = lean_box(0);
v_isShared_903_ = v_isSharedCheck_911_;
goto v_resetjp_901_;
}
v_resetjp_901_:
{
lean_object* v_fst_904_; lean_object* v_snd_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_909_; 
v_fst_904_ = lean_ctor_get(v_a_900_, 0);
lean_inc(v_fst_904_);
v_snd_905_ = lean_ctor_get(v_a_900_, 1);
lean_inc(v_snd_905_);
lean_dec(v_a_900_);
v___x_906_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0));
v___x_907_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_907_, 0, v_snd_905_);
lean_ctor_set(v___x_907_, 1, v_fst_891_);
lean_ctor_set(v___x_907_, 2, v___x_906_);
lean_ctor_set(v___x_907_, 3, v_fst_904_);
if (v_isShared_903_ == 0)
{
lean_ctor_set(v___x_902_, 0, v___x_907_);
v___x_909_ = v___x_902_;
goto v_reusejp_908_;
}
else
{
lean_object* v_reuseFailAlloc_910_; 
v_reuseFailAlloc_910_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_910_, 0, v___x_907_);
v___x_909_ = v_reuseFailAlloc_910_;
goto v_reusejp_908_;
}
v_reusejp_908_:
{
return v___x_909_;
}
}
}
else
{
lean_object* v_a_912_; lean_object* v___x_914_; uint8_t v_isShared_915_; uint8_t v_isSharedCheck_919_; 
lean_dec(v_fst_891_);
v_a_912_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_919_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_919_ == 0)
{
v___x_914_ = v___x_899_;
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
else
{
lean_inc(v_a_912_);
lean_dec(v___x_899_);
v___x_914_ = lean_box(0);
v_isShared_915_ = v_isSharedCheck_919_;
goto v_resetjp_913_;
}
v_resetjp_913_:
{
lean_object* v___x_917_; 
if (v_isShared_915_ == 0)
{
v___x_917_ = v___x_914_;
goto v_reusejp_916_;
}
else
{
lean_object* v_reuseFailAlloc_918_; 
v_reuseFailAlloc_918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_918_, 0, v_a_912_);
v___x_917_ = v_reuseFailAlloc_918_;
goto v_reusejp_916_;
}
v_reusejp_916_:
{
return v___x_917_;
}
}
}
}
else
{
lean_object* v_a_920_; lean_object* v___x_922_; uint8_t v_isShared_923_; uint8_t v_isSharedCheck_927_; 
lean_dec(v_fst_895_);
lean_dec(v_fst_891_);
lean_dec(v_subst_876_);
v_a_920_ = lean_ctor_get(v___x_897_, 0);
v_isSharedCheck_927_ = !lean_is_exclusive(v___x_897_);
if (v_isSharedCheck_927_ == 0)
{
v___x_922_ = v___x_897_;
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
else
{
lean_inc(v_a_920_);
lean_dec(v___x_897_);
v___x_922_ = lean_box(0);
v_isShared_923_ = v_isSharedCheck_927_;
goto v_resetjp_921_;
}
v_resetjp_921_:
{
lean_object* v___x_925_; 
if (v_isShared_923_ == 0)
{
v___x_925_ = v___x_922_;
goto v_reusejp_924_;
}
else
{
lean_object* v_reuseFailAlloc_926_; 
v_reuseFailAlloc_926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_926_, 0, v_a_920_);
v___x_925_ = v_reuseFailAlloc_926_;
goto v_reusejp_924_;
}
v_reusejp_924_:
{
return v___x_925_;
}
}
}
}
else
{
lean_object* v_a_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_935_; 
lean_dec(v_fst_891_);
lean_dec(v_subst_876_);
lean_dec(v___x_875_);
v_a_928_ = lean_ctor_get(v___x_893_, 0);
v_isSharedCheck_935_ = !lean_is_exclusive(v___x_893_);
if (v_isSharedCheck_935_ == 0)
{
v___x_930_ = v___x_893_;
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_a_928_);
lean_dec(v___x_893_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_935_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_933_; 
if (v_isShared_931_ == 0)
{
v___x_933_ = v___x_930_;
goto v_reusejp_932_;
}
else
{
lean_object* v_reuseFailAlloc_934_; 
v_reuseFailAlloc_934_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_934_, 0, v_a_928_);
v___x_933_ = v_reuseFailAlloc_934_;
goto v_reusejp_932_;
}
v_reusejp_932_:
{
return v___x_933_;
}
}
}
}
else
{
lean_object* v_a_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_943_; 
lean_dec(v_subst_876_);
lean_dec(v___x_875_);
v_a_936_ = lean_ctor_get(v___x_889_, 0);
v_isSharedCheck_943_ = !lean_is_exclusive(v___x_889_);
if (v_isSharedCheck_943_ == 0)
{
v___x_938_ = v___x_889_;
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_a_936_);
lean_dec(v___x_889_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_943_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_941_; 
if (v_isShared_939_ == 0)
{
v___x_941_ = v___x_938_;
goto v_reusejp_940_;
}
else
{
lean_object* v_reuseFailAlloc_942_; 
v_reuseFailAlloc_942_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_942_, 0, v_a_936_);
v___x_941_ = v_reuseFailAlloc_942_;
goto v_reusejp_940_;
}
v_reusejp_940_:
{
return v___x_941_;
}
}
}
}
else
{
lean_object* v_a_944_; lean_object* v___x_946_; uint8_t v_isShared_947_; uint8_t v_isSharedCheck_951_; 
lean_dec(v_subst_876_);
lean_dec(v___x_875_);
lean_dec(v___x_873_);
v_a_944_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_951_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_951_ == 0)
{
v___x_946_ = v___x_885_;
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
else
{
lean_inc(v_a_944_);
lean_dec(v___x_885_);
v___x_946_ = lean_box(0);
v_isShared_947_ = v_isSharedCheck_951_;
goto v_resetjp_945_;
}
v_resetjp_945_:
{
lean_object* v___x_949_; 
if (v_isShared_947_ == 0)
{
v___x_949_ = v___x_946_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v_a_944_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
else
{
lean_object* v_a_952_; lean_object* v___x_954_; uint8_t v_isShared_955_; uint8_t v_isSharedCheck_959_; 
lean_dec(v_subst_876_);
lean_dec(v___x_875_);
lean_dec(v_xNamePrefix_874_);
lean_dec(v___x_873_);
lean_dec_ref(v_a_872_);
lean_dec(v_mvarId_871_);
v_a_952_ = lean_ctor_get(v___x_883_, 0);
v_isSharedCheck_959_ = !lean_is_exclusive(v___x_883_);
if (v_isSharedCheck_959_ == 0)
{
v___x_954_ = v___x_883_;
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
else
{
lean_inc(v_a_952_);
lean_dec(v___x_883_);
v___x_954_ = lean_box(0);
v_isShared_955_ = v_isSharedCheck_959_;
goto v_resetjp_953_;
}
v_resetjp_953_:
{
lean_object* v___x_957_; 
if (v_isShared_955_ == 0)
{
v___x_957_ = v___x_954_;
goto v_reusejp_956_;
}
else
{
lean_object* v_reuseFailAlloc_958_; 
v_reuseFailAlloc_958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_958_, 0, v_a_952_);
v___x_957_ = v_reuseFailAlloc_958_;
goto v_reusejp_956_;
}
v_reusejp_956_:
{
return v___x_957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed(lean_object* v___x_960_, lean_object* v_mvarId_961_, lean_object* v_a_962_, lean_object* v___x_963_, lean_object* v_xNamePrefix_964_, lean_object* v___x_965_, lean_object* v_subst_966_, lean_object* v___x_967_, lean_object* v___y_968_, lean_object* v___y_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_){
_start:
{
uint8_t v___x_3711__boxed_973_; lean_object* v_res_974_; 
v___x_3711__boxed_973_ = lean_unbox(v___x_967_);
v_res_974_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(v___x_960_, v_mvarId_961_, v_a_962_, v___x_963_, v_xNamePrefix_964_, v___x_965_, v_subst_966_, v___x_3711__boxed_973_, v___y_968_, v___y_969_, v___y_970_, v___y_971_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
lean_dec(v___y_969_);
lean_dec_ref(v___y_968_);
return v_res_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(lean_object* v_fst_975_, size_t v_sz_976_, size_t v_i_977_, lean_object* v_bs_978_){
_start:
{
uint8_t v___x_979_; 
v___x_979_ = lean_usize_dec_lt(v_i_977_, v_sz_976_);
if (v___x_979_ == 0)
{
return v_bs_978_;
}
else
{
lean_object* v_v_980_; lean_object* v___x_981_; lean_object* v_bs_x27_982_; lean_object* v___x_983_; lean_object* v___x_984_; size_t v___x_985_; size_t v___x_986_; lean_object* v___x_987_; 
v_v_980_ = lean_array_uget(v_bs_978_, v_i_977_);
v___x_981_ = lean_unsigned_to_nat(0u);
v_bs_x27_982_ = lean_array_uset(v_bs_978_, v_i_977_, v___x_981_);
v___x_983_ = l_Lean_Meta_FVarSubst_get(v_fst_975_, v_v_980_);
v___x_984_ = l_Lean_Expr_fvarId_x21(v___x_983_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((size_t)1ULL);
v___x_986_ = lean_usize_add(v_i_977_, v___x_985_);
v___x_987_ = lean_array_uset(v_bs_x27_982_, v_i_977_, v___x_984_);
v_i_977_ = v___x_986_;
v_bs_978_ = v___x_987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1___boxed(lean_object* v_fst_989_, lean_object* v_sz_990_, lean_object* v_i_991_, lean_object* v_bs_992_){
_start:
{
size_t v_sz_boxed_993_; size_t v_i_boxed_994_; lean_object* v_res_995_; 
v_sz_boxed_993_ = lean_unbox_usize(v_sz_990_);
lean_dec(v_sz_990_);
v_i_boxed_994_ = lean_unbox_usize(v_i_991_);
lean_dec(v_i_991_);
v_res_995_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_989_, v_sz_boxed_993_, v_i_boxed_994_, v_bs_992_);
lean_dec(v_fst_989_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(lean_object* v_sizes_996_, lean_object* v_fst_997_, lean_object* v_a_998_, lean_object* v_xNamePrefix_999_, size_t v_sz_1000_, size_t v_i_1001_, lean_object* v_bs_1002_, lean_object* v___y_1003_, lean_object* v___y_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_){
_start:
{
uint8_t v___x_1008_; 
v___x_1008_ = lean_usize_dec_lt(v_i_1001_, v_sz_1000_);
if (v___x_1008_ == 0)
{
lean_object* v___x_1009_; 
lean_dec(v_xNamePrefix_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_fst_997_);
v___x_1009_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1009_, 0, v_bs_1002_);
return v___x_1009_;
}
else
{
lean_object* v_v_1010_; lean_object* v_mvarId_1011_; lean_object* v_newHs_1012_; lean_object* v_subst_1013_; lean_object* v___x_1014_; lean_object* v_bs_x27_1015_; lean_object* v_a_1017_; lean_object* v___x_1022_; lean_object* v___x_1023_; uint8_t v___x_1024_; 
v_v_1010_ = lean_array_uget_borrowed(v_bs_1002_, v_i_1001_);
v_mvarId_1011_ = lean_ctor_get(v_v_1010_, 0);
lean_inc(v_mvarId_1011_);
v_newHs_1012_ = lean_ctor_get(v_v_1010_, 1);
lean_inc_ref(v_newHs_1012_);
v_subst_1013_ = lean_ctor_get(v_v_1010_, 2);
lean_inc(v_subst_1013_);
v___x_1014_ = lean_unsigned_to_nat(0u);
v_bs_x27_1015_ = lean_array_uset(v_bs_1002_, v_i_1001_, v___x_1014_);
v___x_1022_ = lean_usize_to_nat(v_i_1001_);
v___x_1023_ = lean_array_get_size(v_sizes_996_);
v___x_1024_ = lean_nat_dec_lt(v___x_1022_, v___x_1023_);
if (v___x_1024_ == 0)
{
lean_object* v___x_1025_; 
lean_dec(v___x_1022_);
lean_inc(v_fst_997_);
v___x_1025_ = l_Lean_Meta_substCore(v_mvarId_1011_, v_fst_997_, v___x_1024_, v_subst_1013_, v___x_1008_, v___x_1024_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1025_) == 0)
{
lean_object* v_a_1026_; lean_object* v_fst_1027_; lean_object* v_snd_1028_; size_t v_sz_1029_; size_t v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
v_a_1026_ = lean_ctor_get(v___x_1025_, 0);
lean_inc(v_a_1026_);
lean_dec_ref_known(v___x_1025_, 1);
v_fst_1027_ = lean_ctor_get(v_a_1026_, 0);
lean_inc(v_fst_1027_);
v_snd_1028_ = lean_ctor_get(v_a_1026_, 1);
lean_inc(v_snd_1028_);
lean_dec(v_a_1026_);
v_sz_1029_ = lean_array_size(v_newHs_1012_);
v___x_1030_ = ((size_t)0ULL);
v___x_1031_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_1027_, v_sz_1029_, v___x_1030_, v_newHs_1012_);
v___x_1032_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0));
v___x_1033_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1033_, 0, v_snd_1028_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
lean_ctor_set(v___x_1033_, 2, v___x_1031_);
lean_ctor_set(v___x_1033_, 3, v_fst_1027_);
v_a_1017_ = v___x_1033_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1041_; 
lean_dec_ref(v_bs_x27_1015_);
lean_dec_ref(v_newHs_1012_);
lean_dec(v_xNamePrefix_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_fst_997_);
v_a_1034_ = lean_ctor_get(v___x_1025_, 0);
v_isSharedCheck_1041_ = !lean_is_exclusive(v___x_1025_);
if (v_isSharedCheck_1041_ == 0)
{
v___x_1036_ = v___x_1025_;
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_a_1034_);
lean_dec(v___x_1025_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1041_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1039_; 
if (v_isShared_1037_ == 0)
{
v___x_1039_ = v___x_1036_;
goto v_reusejp_1038_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v_a_1034_);
v___x_1039_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1038_;
}
v_reusejp_1038_:
{
return v___x_1039_;
}
}
}
}
else
{
lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___f_1047_; lean_object* v___x_1048_; 
lean_dec_ref(v_newHs_1012_);
lean_inc(v_fst_997_);
v___x_1042_ = l_Lean_Meta_FVarSubst_get(v_subst_1013_, v_fst_997_);
v___x_1043_ = l_Lean_Expr_fvarId_x21(v___x_1042_);
lean_dec_ref(v___x_1042_);
v___x_1044_ = lean_array_fget_borrowed(v_sizes_996_, v___x_1022_);
lean_dec(v___x_1022_);
lean_inc(v___x_1043_);
v___x_1045_ = l_Lean_mkFVar(v___x_1043_);
v___x_1046_ = lean_box(v___x_1008_);
lean_inc(v_xNamePrefix_999_);
lean_inc(v___x_1044_);
lean_inc_ref(v_a_998_);
lean_inc(v_mvarId_1011_);
v___f_1047_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1047_, 0, v___x_1045_);
lean_closure_set(v___f_1047_, 1, v_mvarId_1011_);
lean_closure_set(v___f_1047_, 2, v_a_998_);
lean_closure_set(v___f_1047_, 3, v___x_1044_);
lean_closure_set(v___f_1047_, 4, v_xNamePrefix_999_);
lean_closure_set(v___f_1047_, 5, v___x_1043_);
lean_closure_set(v___f_1047_, 6, v_subst_1013_);
lean_closure_set(v___f_1047_, 7, v___x_1046_);
v___x_1048_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_1011_, v___f_1047_, v___y_1003_, v___y_1004_, v___y_1005_, v___y_1006_);
if (lean_obj_tag(v___x_1048_) == 0)
{
lean_object* v_a_1049_; 
v_a_1049_ = lean_ctor_get(v___x_1048_, 0);
lean_inc(v_a_1049_);
lean_dec_ref_known(v___x_1048_, 1);
v_a_1017_ = v_a_1049_;
goto v___jp_1016_;
}
else
{
lean_object* v_a_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1057_; 
lean_dec_ref(v_bs_x27_1015_);
lean_dec(v_xNamePrefix_999_);
lean_dec_ref(v_a_998_);
lean_dec(v_fst_997_);
v_a_1050_ = lean_ctor_get(v___x_1048_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v___x_1048_);
if (v_isSharedCheck_1057_ == 0)
{
v___x_1052_ = v___x_1048_;
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_a_1050_);
lean_dec(v___x_1048_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1057_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1055_; 
if (v_isShared_1053_ == 0)
{
v___x_1055_ = v___x_1052_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v_a_1050_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
v___jp_1016_:
{
size_t v___x_1018_; size_t v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((size_t)1ULL);
v___x_1019_ = lean_usize_add(v_i_1001_, v___x_1018_);
v___x_1020_ = lean_array_uset(v_bs_x27_1015_, v_i_1001_, v_a_1017_);
v_i_1001_ = v___x_1019_;
v_bs_1002_ = v___x_1020_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___boxed(lean_object* v_sizes_1058_, lean_object* v_fst_1059_, lean_object* v_a_1060_, lean_object* v_xNamePrefix_1061_, lean_object* v_sz_1062_, lean_object* v_i_1063_, lean_object* v_bs_1064_, lean_object* v___y_1065_, lean_object* v___y_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_){
_start:
{
size_t v_sz_boxed_1070_; size_t v_i_boxed_1071_; lean_object* v_res_1072_; 
v_sz_boxed_1070_ = lean_unbox_usize(v_sz_1062_);
lean_dec(v_sz_1062_);
v_i_boxed_1071_ = lean_unbox_usize(v_i_1063_);
lean_dec(v_i_1063_);
v_res_1072_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1058_, v_fst_1059_, v_a_1060_, v_xNamePrefix_1061_, v_sz_boxed_1070_, v_i_boxed_1071_, v_bs_1064_, v___y_1065_, v___y_1066_, v___y_1067_, v___y_1068_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec(v___y_1066_);
lean_dec_ref(v___y_1065_);
lean_dec_ref(v_sizes_1058_);
return v_res_1072_;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = lean_box(0);
v___x_1080_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__3));
v___x_1081_ = l_Lean_mkConst(v___x_1080_, v___x_1079_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0(lean_object* v___x_1085_, lean_object* v___x_1086_, lean_object* v_mvarId_1087_, lean_object* v_sizes_1088_, lean_object* v_hNamePrefix_1089_, lean_object* v_a_1090_, lean_object* v_xNamePrefix_1091_, lean_object* v___y_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = l_Lean_Meta_mkAppM(v___x_1085_, v___x_1086_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1097_) == 0)
{
lean_object* v_a_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v_a_1098_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_a_1098_);
lean_dec_ref_known(v___x_1097_, 1);
v___x_1099_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__1));
v___x_1100_ = lean_obj_once(&l_Lean_Meta_caseArraySizes___lam__0___closed__4, &l_Lean_Meta_caseArraySizes___lam__0___closed__4_once, _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4);
v___x_1101_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__6));
v___x_1102_ = l_Lean_MVarId_assertExt(v_mvarId_1087_, v___x_1099_, v___x_1100_, v_a_1098_, v___x_1101_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1102_) == 0)
{
lean_object* v_a_1103_; uint8_t v___x_1104_; lean_object* v___x_1105_; 
v_a_1103_ = lean_ctor_get(v___x_1102_, 0);
lean_inc(v_a_1103_);
lean_dec_ref_known(v___x_1102_, 1);
v___x_1104_ = 0;
v___x_1105_ = l_Lean_Meta_intro1Core(v_a_1103_, v___x_1104_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1105_) == 0)
{
lean_object* v_a_1106_; lean_object* v_fst_1107_; lean_object* v_snd_1108_; lean_object* v___x_1109_; 
v_a_1106_ = lean_ctor_get(v___x_1105_, 0);
lean_inc(v_a_1106_);
lean_dec_ref_known(v___x_1105_, 1);
v_fst_1107_ = lean_ctor_get(v_a_1106_, 0);
lean_inc(v_fst_1107_);
v_snd_1108_ = lean_ctor_get(v_a_1106_, 1);
lean_inc(v_snd_1108_);
lean_dec(v_a_1106_);
v___x_1109_ = l_Lean_Meta_intro1Core(v_snd_1108_, v___x_1104_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1109_) == 0)
{
lean_object* v_a_1110_; lean_object* v_fst_1111_; lean_object* v_snd_1112_; size_t v_sz_1113_; size_t v___x_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; lean_object* v___x_1117_; 
v_a_1110_ = lean_ctor_get(v___x_1109_, 0);
lean_inc(v_a_1110_);
lean_dec_ref_known(v___x_1109_, 1);
v_fst_1111_ = lean_ctor_get(v_a_1110_, 0);
lean_inc(v_fst_1111_);
v_snd_1112_ = lean_ctor_get(v_a_1110_, 1);
lean_inc(v_snd_1112_);
lean_dec(v_a_1110_);
v_sz_1113_ = lean_array_size(v_sizes_1088_);
v___x_1114_ = ((size_t)0ULL);
lean_inc_ref(v_sizes_1088_);
v___x_1115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_1113_, v___x_1114_, v_sizes_1088_);
v___x_1116_ = 1;
v___x_1117_ = l_Lean_Meta_caseValues(v_snd_1112_, v_fst_1107_, v___x_1115_, v_hNamePrefix_1089_, v___x_1116_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
if (lean_obj_tag(v___x_1117_) == 0)
{
lean_object* v_a_1118_; size_t v_sz_1119_; lean_object* v___x_1120_; 
v_a_1118_ = lean_ctor_get(v___x_1117_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v___x_1117_, 1);
v_sz_1119_ = lean_array_size(v_a_1118_);
v___x_1120_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1088_, v_fst_1111_, v_a_1090_, v_xNamePrefix_1091_, v_sz_1119_, v___x_1114_, v_a_1118_, v___y_1092_, v___y_1093_, v___y_1094_, v___y_1095_);
lean_dec_ref(v_sizes_1088_);
return v___x_1120_;
}
else
{
lean_object* v_a_1121_; lean_object* v___x_1123_; uint8_t v_isShared_1124_; uint8_t v_isSharedCheck_1128_; 
lean_dec(v_fst_1111_);
lean_dec(v_xNamePrefix_1091_);
lean_dec_ref(v_a_1090_);
lean_dec_ref(v_sizes_1088_);
v_a_1121_ = lean_ctor_get(v___x_1117_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v___x_1117_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1123_ = v___x_1117_;
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
else
{
lean_inc(v_a_1121_);
lean_dec(v___x_1117_);
v___x_1123_ = lean_box(0);
v_isShared_1124_ = v_isSharedCheck_1128_;
goto v_resetjp_1122_;
}
v_resetjp_1122_:
{
lean_object* v___x_1126_; 
if (v_isShared_1124_ == 0)
{
v___x_1126_ = v___x_1123_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v_a_1121_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
else
{
lean_object* v_a_1129_; lean_object* v___x_1131_; uint8_t v_isShared_1132_; uint8_t v_isSharedCheck_1136_; 
lean_dec(v_fst_1107_);
lean_dec(v_xNamePrefix_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_hNamePrefix_1089_);
lean_dec_ref(v_sizes_1088_);
v_a_1129_ = lean_ctor_get(v___x_1109_, 0);
v_isSharedCheck_1136_ = !lean_is_exclusive(v___x_1109_);
if (v_isSharedCheck_1136_ == 0)
{
v___x_1131_ = v___x_1109_;
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
else
{
lean_inc(v_a_1129_);
lean_dec(v___x_1109_);
v___x_1131_ = lean_box(0);
v_isShared_1132_ = v_isSharedCheck_1136_;
goto v_resetjp_1130_;
}
v_resetjp_1130_:
{
lean_object* v___x_1134_; 
if (v_isShared_1132_ == 0)
{
v___x_1134_ = v___x_1131_;
goto v_reusejp_1133_;
}
else
{
lean_object* v_reuseFailAlloc_1135_; 
v_reuseFailAlloc_1135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1135_, 0, v_a_1129_);
v___x_1134_ = v_reuseFailAlloc_1135_;
goto v_reusejp_1133_;
}
v_reusejp_1133_:
{
return v___x_1134_;
}
}
}
}
else
{
lean_object* v_a_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1144_; 
lean_dec(v_xNamePrefix_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_hNamePrefix_1089_);
lean_dec_ref(v_sizes_1088_);
v_a_1137_ = lean_ctor_get(v___x_1105_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1105_);
if (v_isSharedCheck_1144_ == 0)
{
v___x_1139_ = v___x_1105_;
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_a_1137_);
lean_dec(v___x_1105_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1144_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v___x_1142_; 
if (v_isShared_1140_ == 0)
{
v___x_1142_ = v___x_1139_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_a_1137_);
v___x_1142_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
return v___x_1142_;
}
}
}
}
else
{
lean_object* v_a_1145_; lean_object* v___x_1147_; uint8_t v_isShared_1148_; uint8_t v_isSharedCheck_1152_; 
lean_dec(v_xNamePrefix_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_hNamePrefix_1089_);
lean_dec_ref(v_sizes_1088_);
v_a_1145_ = lean_ctor_get(v___x_1102_, 0);
v_isSharedCheck_1152_ = !lean_is_exclusive(v___x_1102_);
if (v_isSharedCheck_1152_ == 0)
{
v___x_1147_ = v___x_1102_;
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
else
{
lean_inc(v_a_1145_);
lean_dec(v___x_1102_);
v___x_1147_ = lean_box(0);
v_isShared_1148_ = v_isSharedCheck_1152_;
goto v_resetjp_1146_;
}
v_resetjp_1146_:
{
lean_object* v___x_1150_; 
if (v_isShared_1148_ == 0)
{
v___x_1150_ = v___x_1147_;
goto v_reusejp_1149_;
}
else
{
lean_object* v_reuseFailAlloc_1151_; 
v_reuseFailAlloc_1151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1151_, 0, v_a_1145_);
v___x_1150_ = v_reuseFailAlloc_1151_;
goto v_reusejp_1149_;
}
v_reusejp_1149_:
{
return v___x_1150_;
}
}
}
}
else
{
lean_object* v_a_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1160_; 
lean_dec(v_xNamePrefix_1091_);
lean_dec_ref(v_a_1090_);
lean_dec(v_hNamePrefix_1089_);
lean_dec_ref(v_sizes_1088_);
lean_dec(v_mvarId_1087_);
v_a_1153_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1160_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1160_ == 0)
{
v___x_1155_ = v___x_1097_;
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_a_1153_);
lean_dec(v___x_1097_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1160_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
lean_object* v___x_1158_; 
if (v_isShared_1156_ == 0)
{
v___x_1158_ = v___x_1155_;
goto v_reusejp_1157_;
}
else
{
lean_object* v_reuseFailAlloc_1159_; 
v_reuseFailAlloc_1159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1159_, 0, v_a_1153_);
v___x_1158_ = v_reuseFailAlloc_1159_;
goto v_reusejp_1157_;
}
v_reusejp_1157_:
{
return v___x_1158_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0___boxed(lean_object* v___x_1161_, lean_object* v___x_1162_, lean_object* v_mvarId_1163_, lean_object* v_sizes_1164_, lean_object* v_hNamePrefix_1165_, lean_object* v_a_1166_, lean_object* v_xNamePrefix_1167_, lean_object* v___y_1168_, lean_object* v___y_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l_Lean_Meta_caseArraySizes___lam__0(v___x_1161_, v___x_1162_, v_mvarId_1163_, v_sizes_1164_, v_hNamePrefix_1165_, v_a_1166_, v_xNamePrefix_1167_, v___y_1168_, v___y_1169_, v___y_1170_, v___y_1171_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
lean_dec(v___y_1169_);
lean_dec_ref(v___y_1168_);
return v_res_1173_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes(lean_object* v_mvarId_1178_, lean_object* v_fvarId_1179_, lean_object* v_sizes_1180_, lean_object* v_xNamePrefix_1181_, lean_object* v_hNamePrefix_1182_, lean_object* v_a_1183_, lean_object* v_a_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_){
_start:
{
lean_object* v_a_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; 
v_a_1188_ = l_Lean_mkFVar(v_fvarId_1179_);
v___x_1189_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___closed__1));
v___x_1190_ = lean_unsigned_to_nat(1u);
v___x_1191_ = lean_mk_empty_array_with_capacity(v___x_1190_);
lean_inc_ref(v_a_1188_);
v___x_1192_ = lean_array_push(v___x_1191_, v_a_1188_);
lean_inc(v_mvarId_1178_);
v___f_1193_ = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1193_, 0, v___x_1189_);
lean_closure_set(v___f_1193_, 1, v___x_1192_);
lean_closure_set(v___f_1193_, 2, v_mvarId_1178_);
lean_closure_set(v___f_1193_, 3, v_sizes_1180_);
lean_closure_set(v___f_1193_, 4, v_hNamePrefix_1182_);
lean_closure_set(v___f_1193_, 5, v_a_1188_);
lean_closure_set(v___f_1193_, 6, v_xNamePrefix_1181_);
v___x_1194_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_1178_, v___f_1193_, v_a_1183_, v_a_1184_, v_a_1185_, v_a_1186_);
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___boxed(lean_object* v_mvarId_1195_, lean_object* v_fvarId_1196_, lean_object* v_sizes_1197_, lean_object* v_xNamePrefix_1198_, lean_object* v_hNamePrefix_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_Lean_Meta_caseArraySizes(v_mvarId_1195_, v_fvarId_1196_, v_sizes_1197_, v_xNamePrefix_1198_, v_hNamePrefix_1199_, v_a_1200_, v_a_1201_, v_a_1202_, v_a_1203_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
lean_dec(v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3(lean_object* v_sizes_1206_, lean_object* v_fst_1207_, lean_object* v_a_1208_, lean_object* v_xNamePrefix_1209_, lean_object* v_as_1210_, size_t v_sz_1211_, size_t v_i_1212_, lean_object* v_bs_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_){
_start:
{
lean_object* v___x_1219_; 
v___x_1219_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1206_, v_fst_1207_, v_a_1208_, v_xNamePrefix_1209_, v_sz_1211_, v_i_1212_, v_bs_1213_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___boxed(lean_object* v_sizes_1220_, lean_object* v_fst_1221_, lean_object* v_a_1222_, lean_object* v_xNamePrefix_1223_, lean_object* v_as_1224_, lean_object* v_sz_1225_, lean_object* v_i_1226_, lean_object* v_bs_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
size_t v_sz_boxed_1233_; size_t v_i_boxed_1234_; lean_object* v_res_1235_; 
v_sz_boxed_1233_ = lean_unbox_usize(v_sz_1225_);
lean_dec(v_sz_1225_);
v_i_boxed_1234_ = lean_unbox_usize(v_i_1226_);
lean_dec(v_i_1226_);
v_res_1235_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3(v_sizes_1220_, v_fst_1221_, v_a_1222_, v_xNamePrefix_1223_, v_as_1224_, v_sz_boxed_1233_, v_i_boxed_1234_, v_bs_1227_, v___y_1228_, v___y_1229_, v___y_1230_, v___y_1231_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec(v___y_1229_);
lean_dec_ref(v___y_1228_);
lean_dec_ref(v_as_1224_);
lean_dec_ref(v_sizes_1220_);
return v_res_1235_;
}
}
lean_object* runtime_initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Match_CaseValues(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_CaseValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_FVarSubst(uint8_t builtin);
lean_object* initialize_Lean_Meta_Match_CaseValues(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Match_CaseArraySizes(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_FVarSubst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Match_CaseValues(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Match_CaseArraySizes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Match_CaseArraySizes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Match_CaseArraySizes(builtin);
}
#ifdef __cplusplus
}
#endif
