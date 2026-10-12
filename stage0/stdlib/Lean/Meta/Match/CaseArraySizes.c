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
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
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
lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(lean_object* v_msgData_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
_start:
{
lean_object* v___x_15_; lean_object* v_env_16_; uint8_t v___x_17_; lean_object* v_env_18_; lean_object* v___x_19_; lean_object* v_toCold_20_; lean_object* v_mctx_21_; lean_object* v_lctx_22_; lean_object* v_options_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; 
v___x_15_ = lean_st_ref_get(v___y_13_);
v_env_16_ = lean_ctor_get(v___x_15_, 0);
lean_inc_ref(v_env_16_);
lean_dec(v___x_15_);
v___x_17_ = 0;
v_env_18_ = l_Lean_Environment_setRecordingDeps(v_env_16_, v___x_17_);
v___x_19_ = lean_st_ref_get(v___y_11_);
v_toCold_20_ = lean_ctor_get(v___y_12_, 0);
v_mctx_21_ = lean_ctor_get(v___x_19_, 0);
lean_inc_ref(v_mctx_21_);
lean_dec(v___x_19_);
v_lctx_22_ = lean_ctor_get(v___y_10_, 2);
v_options_23_ = lean_ctor_get(v_toCold_20_, 2);
lean_inc_ref(v_options_23_);
lean_inc_ref(v_lctx_22_);
v___x_24_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_24_, 0, v_env_18_);
lean_ctor_set(v___x_24_, 1, v_mctx_21_);
lean_ctor_set(v___x_24_, 2, v_lctx_22_);
lean_ctor_set(v___x_24_, 3, v_options_23_);
v___x_25_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
lean_ctor_set(v___x_25_, 1, v_msgData_9_);
v___x_26_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_26_, 0, v___x_25_);
return v___x_26_;
}
}
LEAN_EXPORT void l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msgData_9_ = stack[0].m_obj;
lean_object* v___y_10_ = stack[1].m_obj;
lean_object* v___y_11_ = stack[2].m_obj;
lean_object* v___y_12_ = stack[3].m_obj;
lean_object* v___y_13_ = stack[4].m_obj;
lean_object* v_res_27_;
v_res_27_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msgData_9_, v___y_10_, v___y_11_, v___y_12_, v___y_13_);
stack->m_obj
 = v_res_27_;
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0___boxed(lean_object* v_msgData_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_, lean_object* v___y_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msgData_28_, v___y_29_, v___y_30_, v___y_31_, v___y_32_);
lean_dec(v___y_32_);
lean_dec_ref(v___y_31_);
lean_dec(v___y_30_);
lean_dec_ref(v___y_29_);
return v_res_34_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(lean_object* v_msg_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_, lean_object* v___y_39_){
_start:
{
lean_object* v_ref_41_; lean_object* v___x_42_; lean_object* v_a_43_; lean_object* v___x_45_; uint8_t v_isShared_46_; uint8_t v_isSharedCheck_51_; 
v_ref_41_ = lean_ctor_get(v___y_38_, 2);
v___x_42_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msg_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
v_a_43_ = lean_ctor_get(v___x_42_, 0);
v_isSharedCheck_51_ = !lean_is_exclusive(v___x_42_);
if (v_isSharedCheck_51_ == 0)
{
v___x_45_ = v___x_42_;
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
else
{
lean_inc(v_a_43_);
lean_dec(v___x_42_);
v___x_45_ = lean_box(0);
v_isShared_46_ = v_isSharedCheck_51_;
goto v_resetjp_44_;
}
v_resetjp_44_:
{
lean_object* v___x_47_; lean_object* v___x_49_; 
lean_inc(v_ref_41_);
v___x_47_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_47_, 0, v_ref_41_);
lean_ctor_set(v___x_47_, 1, v_a_43_);
if (v_isShared_46_ == 0)
{
lean_ctor_set_tag(v___x_45_, 1);
lean_ctor_set(v___x_45_, 0, v___x_47_);
v___x_49_ = v___x_45_;
goto v_reusejp_48_;
}
else
{
lean_object* v_reuseFailAlloc_50_; 
v_reuseFailAlloc_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_50_, 0, v___x_47_);
v___x_49_ = v_reuseFailAlloc_50_;
goto v_reusejp_48_;
}
v_reusejp_48_:
{
return v___x_49_;
}
}
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_35_ = stack[0].m_obj;
lean_object* v___y_36_ = stack[1].m_obj;
lean_object* v___y_37_ = stack[2].m_obj;
lean_object* v___y_38_ = stack[3].m_obj;
lean_object* v___y_39_ = stack[4].m_obj;
lean_object* v_res_52_;
v_res_52_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_35_, v___y_36_, v___y_37_, v___y_38_, v___y_39_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg___boxed(lean_object* v_msg_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_, lean_object* v___y_57_, lean_object* v___y_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_53_, v___y_54_, v___y_55_, v___y_56_, v___y_57_);
lean_dec(v___y_57_);
lean_dec_ref(v___y_56_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
return v_res_59_;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__3(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; 
v___x_64_ = ((lean_object*)(l_Lean_Meta_getArrayArgType___closed__2));
v___x_65_ = l_Lean_stringToMessageData(v___x_64_);
return v___x_65_;
}
}
lean_object* l_Lean_Meta_getArrayArgType(lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_, lean_object* v_a_69_, lean_object* v_a_70_){
_start:
{
lean_object* v___x_72_; 
lean_inc(v_a_70_);
lean_inc_ref(v_a_69_);
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
lean_inc_ref(v_a_66_);
v___x_72_ = lean_infer_type(v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_74_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
lean_inc(v_a_73_);
lean_dec_ref_known(v___x_72_, 1);
v___x_74_ = l_Lean_Meta_whnfD(v_a_73_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
if (lean_obj_tag(v___x_74_) == 0)
{
lean_object* v_a_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_99_; 
v_a_75_ = lean_ctor_get(v___x_74_, 0);
v_isSharedCheck_99_ = !lean_is_exclusive(v___x_74_);
if (v_isSharedCheck_99_ == 0)
{
v___x_77_ = v___x_74_;
v_isShared_78_ = v_isSharedCheck_99_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_a_75_);
lean_dec(v___x_74_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_99_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_84_; lean_object* v___x_85_; uint8_t v___x_86_; 
v___x_84_ = ((lean_object*)(l_Lean_Meta_getArrayArgType___closed__1));
v___x_85_ = lean_unsigned_to_nat(1u);
v___x_86_ = l_Lean_Expr_isAppOfArity(v_a_75_, v___x_84_, v___x_85_);
if (v___x_86_ == 0)
{
lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v_a_91_; lean_object* v___x_93_; uint8_t v_isShared_94_; uint8_t v_isSharedCheck_98_; 
lean_del_object(v___x_77_);
lean_dec(v_a_75_);
v___x_87_ = lean_obj_once(&l_Lean_Meta_getArrayArgType___closed__3, &l_Lean_Meta_getArrayArgType___closed__3_once, _init_l_Lean_Meta_getArrayArgType___closed__3);
v___x_88_ = l_Lean_indentExpr(v_a_66_);
v___x_89_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_89_, 0, v___x_87_);
lean_ctor_set(v___x_89_, 1, v___x_88_);
v___x_90_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v___x_89_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
v_a_91_ = lean_ctor_get(v___x_90_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v___x_90_);
if (v_isSharedCheck_98_ == 0)
{
v___x_93_ = v___x_90_;
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
else
{
lean_inc(v_a_91_);
lean_dec(v___x_90_);
v___x_93_ = lean_box(0);
v_isShared_94_ = v_isSharedCheck_98_;
goto v_resetjp_92_;
}
v_resetjp_92_:
{
lean_object* v___x_96_; 
if (v_isShared_94_ == 0)
{
v___x_96_ = v___x_93_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_a_91_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
}
else
{
lean_dec_ref(v_a_66_);
goto v___jp_79_;
}
v___jp_79_:
{
lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_80_ = l_Lean_Expr_appArg_x21(v_a_75_);
lean_dec(v_a_75_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v___x_80_);
v___x_82_ = v___x_77_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
}
else
{
lean_dec_ref(v_a_66_);
return v___x_74_;
}
}
else
{
lean_dec_ref(v_a_66_);
return v___x_72_;
}
}
}
LEAN_EXPORT void l_Lean_Meta_getArrayArgType_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_66_ = stack[0].m_obj;
lean_object* v_a_67_ = stack[1].m_obj;
lean_object* v_a_68_ = stack[2].m_obj;
lean_object* v_a_69_ = stack[3].m_obj;
lean_object* v_a_70_ = stack[4].m_obj;
lean_object* v_res_100_;
v_res_100_ = l_Lean_Meta_getArrayArgType(v_a_66_, v_a_67_, v_a_68_, v_a_69_, v_a_70_);
stack->m_obj
 = v_res_100_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType___boxed(lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
lean_object* v_res_107_; 
v_res_107_ = l_Lean_Meta_getArrayArgType(v_a_101_, v_a_102_, v_a_103_, v_a_104_, v_a_105_);
lean_dec(v_a_105_);
lean_dec_ref(v_a_104_);
lean_dec(v_a_103_);
lean_dec_ref(v_a_102_);
return v_res_107_;
}
}
lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(lean_object* v_00_u03b1_108_, lean_object* v_msg_109_, lean_object* v___y_110_, lean_object* v___y_111_, lean_object* v___y_112_, lean_object* v___y_113_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
return v___x_115_;
}
}
LEAN_EXPORT void l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_msg_109_ = stack[1].m_obj;
lean_object* v___y_110_ = stack[2].m_obj;
lean_object* v___y_111_ = stack[3].m_obj;
lean_object* v___y_112_ = stack[4].m_obj;
lean_object* v___y_113_ = stack[5].m_obj;
lean_object* v_res_116_;
v_res_116_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(lean_box(0), v_msg_109_, v___y_110_, v___y_111_, v___y_112_, v___y_113_);
stack->m_obj
 = v_res_116_;
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___boxed(lean_object* v_00_u03b1_117_, lean_object* v_msg_118_, lean_object* v___y_119_, lean_object* v___y_120_, lean_object* v___y_121_, lean_object* v___y_122_, lean_object* v___y_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(v_00_u03b1_117_, v_msg_118_, v___y_119_, v___y_120_, v___y_121_, v___y_122_);
lean_dec(v___y_122_);
lean_dec_ref(v___y_121_);
lean_dec(v___y_120_);
lean_dec_ref(v___y_119_);
return v_res_124_;
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object* v_a_129_, lean_object* v_i_130_, lean_object* v_n_131_, lean_object* v_h_132_, lean_object* v_a_133_, lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_){
_start:
{
lean_object* v___x_138_; lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_138_ = l_Lean_mkRawNatLit(v_i_130_);
v___x_139_ = l_Lean_mkRawNatLit(v_n_131_);
lean_inc_ref(v___x_138_);
v___x_140_ = l_Lean_Meta_mkLt(v___x_138_, v___x_139_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_140_) == 0)
{
lean_object* v_a_141_; lean_object* v___x_142_; 
v_a_141_ = lean_ctor_get(v___x_140_, 0);
lean_inc(v_a_141_);
lean_dec_ref_known(v___x_140_, 1);
v___x_142_ = l_Lean_Meta_mkDecideProof(v_a_141_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
if (lean_obj_tag(v___x_142_) == 0)
{
lean_object* v_a_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v_a_143_ = lean_ctor_get(v___x_142_, 0);
lean_inc(v_a_143_);
lean_dec_ref_known(v___x_142_, 1);
v___x_144_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1));
v___x_145_ = lean_unsigned_to_nat(4u);
v___x_146_ = lean_mk_empty_array_with_capacity(v___x_145_);
v___x_147_ = lean_array_push(v___x_146_, v_a_129_);
v___x_148_ = lean_array_push(v___x_147_, v___x_138_);
v___x_149_ = lean_array_push(v___x_148_, v_h_132_);
v___x_150_ = lean_array_push(v___x_149_, v_a_143_);
v___x_151_ = l_Lean_Meta_mkAppM(v___x_144_, v___x_150_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
return v___x_151_;
}
else
{
lean_dec_ref(v___x_138_);
lean_dec_ref(v_h_132_);
lean_dec_ref(v_a_129_);
return v___x_142_;
}
}
else
{
lean_dec_ref(v___x_138_);
lean_dec_ref(v_h_132_);
lean_dec_ref(v_a_129_);
return v___x_140_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_129_ = stack[0].m_obj;
lean_object* v_i_130_ = stack[1].m_obj;
lean_object* v_n_131_ = stack[2].m_obj;
lean_object* v_h_132_ = stack[3].m_obj;
lean_object* v_a_133_ = stack[4].m_obj;
lean_object* v_a_134_ = stack[5].m_obj;
lean_object* v_a_135_ = stack[6].m_obj;
lean_object* v_a_136_ = stack[7].m_obj;
lean_object* v_res_152_;
v_res_152_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_129_, v_i_130_, v_n_131_, v_h_132_, v_a_133_, v_a_134_, v_a_135_, v_a_136_);
stack->m_obj
 = v_res_152_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___boxed(lean_object* v_a_153_, lean_object* v_i_154_, lean_object* v_n_155_, lean_object* v_h_156_, lean_object* v_a_157_, lean_object* v_a_158_, lean_object* v_a_159_, lean_object* v_a_160_, lean_object* v_a_161_){
_start:
{
lean_object* v_res_162_; 
v_res_162_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_153_, v_i_154_, v_n_155_, v_h_156_, v_a_157_, v_a_158_, v_a_159_, v_a_160_);
lean_dec(v_a_160_);
lean_dec_ref(v_a_159_);
lean_dec(v_a_158_);
lean_dec_ref(v_a_157_);
return v_res_162_;
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(lean_object* v_mvarId_163_, lean_object* v_xs_164_, uint8_t v___x_165_, lean_object* v_args_166_, lean_object* v_a_167_, lean_object* v_heq_168_, lean_object* v___y_169_, lean_object* v___y_170_, lean_object* v___y_171_, lean_object* v___y_172_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_Lean_MVarId_getType(v_mvarId_163_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_176_; uint8_t v___x_177_; uint8_t v___x_178_; lean_object* v___x_179_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
lean_inc(v_a_175_);
lean_dec_ref_known(v___x_174_, 1);
v___x_176_ = lean_array_push(v_xs_164_, v_heq_168_);
v___x_177_ = 1;
v___x_178_ = 1;
v___x_179_ = l_Lean_Meta_mkForallFVars(v___x_176_, v_a_175_, v___x_165_, v___x_177_, v___x_177_, v___x_178_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
lean_dec_ref(v___x_176_);
if (lean_obj_tag(v___x_179_) == 0)
{
lean_object* v_a_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_189_; 
v_a_180_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_189_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_189_ == 0)
{
v___x_182_ = v___x_179_;
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_a_180_);
lean_dec(v___x_179_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_189_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_187_; 
v___x_184_ = lean_array_push(v_args_166_, v_a_167_);
v___x_185_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_185_, 0, v_a_180_);
lean_ctor_set(v___x_185_, 1, v___x_184_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 0, v___x_185_);
v___x_187_ = v___x_182_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_188_; 
v_reuseFailAlloc_188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_188_, 0, v___x_185_);
v___x_187_ = v_reuseFailAlloc_188_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
return v___x_187_;
}
}
}
else
{
lean_object* v_a_190_; lean_object* v___x_192_; uint8_t v_isShared_193_; uint8_t v_isSharedCheck_197_; 
lean_dec_ref(v_a_167_);
lean_dec_ref(v_args_166_);
v_a_190_ = lean_ctor_get(v___x_179_, 0);
v_isSharedCheck_197_ = !lean_is_exclusive(v___x_179_);
if (v_isSharedCheck_197_ == 0)
{
v___x_192_ = v___x_179_;
v_isShared_193_ = v_isSharedCheck_197_;
goto v_resetjp_191_;
}
else
{
lean_inc(v_a_190_);
lean_dec(v___x_179_);
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
else
{
lean_object* v_a_198_; lean_object* v___x_200_; uint8_t v_isShared_201_; uint8_t v_isSharedCheck_205_; 
lean_dec_ref(v_heq_168_);
lean_dec_ref(v_a_167_);
lean_dec_ref(v_args_166_);
lean_dec_ref(v_xs_164_);
v_a_198_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_205_ == 0)
{
v___x_200_ = v___x_174_;
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
else
{
lean_inc(v_a_198_);
lean_dec(v___x_174_);
v___x_200_ = lean_box(0);
v_isShared_201_ = v_isSharedCheck_205_;
goto v_resetjp_199_;
}
v_resetjp_199_:
{
lean_object* v___x_203_; 
if (v_isShared_201_ == 0)
{
v___x_203_ = v___x_200_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v_a_198_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
return v___x_203_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_163_ = stack[0].m_obj;
lean_object* v_xs_164_ = stack[1].m_obj;
uint8_t v___x_165_ = stack[2].m_num;
lean_object* v_args_166_ = stack[3].m_obj;
lean_object* v_a_167_ = stack[4].m_obj;
lean_object* v_heq_168_ = stack[5].m_obj;
lean_object* v___y_169_ = stack[6].m_obj;
lean_object* v___y_170_ = stack[7].m_obj;
lean_object* v___y_171_ = stack[8].m_obj;
lean_object* v___y_172_ = stack[9].m_obj;
lean_object* v_res_206_;
v_res_206_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(v_mvarId_163_, v_xs_164_, v___x_165_, v_args_166_, v_a_167_, v_heq_168_, v___y_169_, v___y_170_, v___y_171_, v___y_172_);
stack->m_obj
 = v_res_206_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(lean_object* v_mvarId_207_, lean_object* v_xs_208_, lean_object* v___x_209_, lean_object* v_args_210_, lean_object* v_a_211_, lean_object* v_heq_212_, lean_object* v___y_213_, lean_object* v___y_214_, lean_object* v___y_215_, lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
uint8_t v___x_1166__boxed_218_; lean_object* v_res_219_; 
v___x_1166__boxed_218_ = lean_unbox(v___x_209_);
v_res_219_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(v_mvarId_207_, v_xs_208_, v___x_1166__boxed_218_, v_args_210_, v_a_211_, v_heq_212_, v___y_213_, v___y_214_, v___y_215_, v___y_216_);
lean_dec(v___y_216_);
lean_dec_ref(v___y_215_);
lean_dec(v___y_214_);
lean_dec_ref(v___y_213_);
return v_res_219_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_220_, lean_object* v_b_221_, lean_object* v___y_222_, lean_object* v___y_223_, lean_object* v___y_224_, lean_object* v___y_225_){
_start:
{
lean_object* v___x_227_; 
lean_inc(v___y_225_);
lean_inc_ref(v___y_224_);
lean_inc(v___y_223_);
lean_inc_ref(v___y_222_);
v___x_227_ = lean_apply_6(v_k_220_, v_b_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_, lean_box(0));
return v___x_227_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_k_220_ = stack[0].m_obj;
lean_object* v_b_221_ = stack[1].m_obj;
lean_object* v___y_222_ = stack[2].m_obj;
lean_object* v___y_223_ = stack[3].m_obj;
lean_object* v___y_224_ = stack[4].m_obj;
lean_object* v___y_225_ = stack[5].m_obj;
lean_object* v_res_228_;
v_res_228_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(v_k_220_, v_b_221_, v___y_222_, v___y_223_, v___y_224_, v___y_225_);
stack->m_obj
 = v_res_228_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_229_, lean_object* v_b_230_, lean_object* v___y_231_, lean_object* v___y_232_, lean_object* v___y_233_, lean_object* v___y_234_, lean_object* v___y_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(v_k_229_, v_b_230_, v___y_231_, v___y_232_, v___y_233_, v___y_234_);
lean_dec(v___y_234_);
lean_dec_ref(v___y_233_);
lean_dec(v___y_232_);
lean_dec_ref(v___y_231_);
return v_res_236_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(lean_object* v_name_237_, uint8_t v_bi_238_, lean_object* v_type_239_, lean_object* v_k_240_, uint8_t v_kind_241_, lean_object* v___y_242_, lean_object* v___y_243_, lean_object* v___y_244_, lean_object* v___y_245_){
_start:
{
lean_object* v___f_247_; lean_object* v___x_248_; 
v___f_247_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_247_, 0, v_k_240_);
v___x_248_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_237_, v_bi_238_, v_type_239_, v___f_247_, v_kind_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
if (lean_obj_tag(v___x_248_) == 0)
{
lean_object* v_a_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_256_; 
v_a_249_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_256_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_256_ == 0)
{
v___x_251_ = v___x_248_;
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_a_249_);
lean_dec(v___x_248_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_256_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_254_; 
if (v_isShared_252_ == 0)
{
v___x_254_ = v___x_251_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_a_249_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
else
{
lean_object* v_a_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_264_; 
v_a_257_ = lean_ctor_get(v___x_248_, 0);
v_isSharedCheck_264_ = !lean_is_exclusive(v___x_248_);
if (v_isSharedCheck_264_ == 0)
{
v___x_259_ = v___x_248_;
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_a_257_);
lean_dec(v___x_248_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_264_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_260_ == 0)
{
v___x_262_ = v___x_259_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_a_257_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_237_ = stack[0].m_obj;
uint8_t v_bi_238_ = stack[1].m_num;
lean_object* v_type_239_ = stack[2].m_obj;
lean_object* v_k_240_ = stack[3].m_obj;
uint8_t v_kind_241_ = stack[4].m_num;
lean_object* v___y_242_ = stack[5].m_obj;
lean_object* v___y_243_ = stack[6].m_obj;
lean_object* v___y_244_ = stack[7].m_obj;
lean_object* v___y_245_ = stack[8].m_obj;
lean_object* v_res_265_;
v_res_265_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_237_, v_bi_238_, v_type_239_, v_k_240_, v_kind_241_, v___y_242_, v___y_243_, v___y_244_, v___y_245_);
stack->m_obj
 = v_res_265_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_266_, lean_object* v_bi_267_, lean_object* v_type_268_, lean_object* v_k_269_, lean_object* v_kind_270_, lean_object* v___y_271_, lean_object* v___y_272_, lean_object* v___y_273_, lean_object* v___y_274_, lean_object* v___y_275_){
_start:
{
uint8_t v_bi_boxed_276_; uint8_t v_kind_boxed_277_; lean_object* v_res_278_; 
v_bi_boxed_276_ = lean_unbox(v_bi_267_);
v_kind_boxed_277_ = lean_unbox(v_kind_270_);
v_res_278_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_266_, v_bi_boxed_276_, v_type_268_, v_k_269_, v_kind_boxed_277_, v___y_271_, v___y_272_, v___y_273_, v___y_274_);
lean_dec(v___y_274_);
lean_dec_ref(v___y_273_);
lean_dec(v___y_272_);
lean_dec_ref(v___y_271_);
return v_res_278_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(lean_object* v_name_279_, lean_object* v_type_280_, lean_object* v_k_281_, lean_object* v___y_282_, lean_object* v___y_283_, lean_object* v___y_284_, lean_object* v___y_285_){
_start:
{
uint8_t v___x_287_; uint8_t v___x_288_; lean_object* v___x_289_; 
v___x_287_ = 0;
v___x_288_ = 0;
v___x_289_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_279_, v___x_287_, v_type_280_, v_k_281_, v___x_288_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
return v___x_289_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_279_ = stack[0].m_obj;
lean_object* v_type_280_ = stack[1].m_obj;
lean_object* v_k_281_ = stack[2].m_obj;
lean_object* v___y_282_ = stack[3].m_obj;
lean_object* v___y_283_ = stack[4].m_obj;
lean_object* v___y_284_ = stack[5].m_obj;
lean_object* v___y_285_ = stack[6].m_obj;
lean_object* v_res_290_;
v_res_290_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_279_, v_type_280_, v_k_281_, v___y_282_, v___y_283_, v___y_284_, v___y_285_);
stack->m_obj
 = v_res_290_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg___boxed(lean_object* v_name_291_, lean_object* v_type_292_, lean_object* v_k_293_, lean_object* v___y_294_, lean_object* v___y_295_, lean_object* v___y_296_, lean_object* v___y_297_, lean_object* v___y_298_){
_start:
{
lean_object* v_res_299_; 
v_res_299_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_291_, v_type_292_, v_k_293_, v___y_294_, v___y_295_, v___y_296_, v___y_297_);
lean_dec(v___y_297_);
lean_dec_ref(v___y_296_);
lean_dec(v___y_295_);
lean_dec_ref(v___y_294_);
return v_res_299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed(lean_object* v_xs_307_, lean_object* v_a_308_, lean_object* v_i_309_, lean_object* v_n_310_, lean_object* v_aSizeEqN_311_, lean_object* v_args_312_, lean_object* v_mvarId_313_, lean_object* v_xNamePrefix_314_, lean_object* v_00_u03b1_315_, lean_object* v___x_316_, lean_object* v_xi_317_, lean_object* v___y_318_, lean_object* v___y_319_, lean_object* v___y_320_, lean_object* v___y_321_, lean_object* v___y_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(v_xs_307_, v_a_308_, v_i_309_, v_n_310_, v_aSizeEqN_311_, v_args_312_, v_mvarId_313_, v_xNamePrefix_314_, v_00_u03b1_315_, v___x_316_, v_xi_317_, v___y_318_, v___y_319_, v___y_320_, v___y_321_);
lean_dec(v___y_321_);
lean_dec_ref(v___y_320_);
lean_dec(v___y_319_);
lean_dec_ref(v___y_318_);
return v_res_323_;
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object* v_mvarId_324_, lean_object* v_a_325_, lean_object* v_n_326_, lean_object* v_xNamePrefix_327_, lean_object* v_aSizeEqN_328_, lean_object* v_00_u03b1_329_, lean_object* v_i_330_, lean_object* v_xs_331_, lean_object* v_args_332_, lean_object* v_a_333_, lean_object* v_a_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = lean_nat_dec_lt(v_i_330_, v_n_326_);
if (v___x_338_ == 0)
{
lean_object* v___x_339_; lean_object* v___x_340_; 
lean_dec(v_i_330_);
lean_dec(v_xNamePrefix_327_);
lean_inc_ref(v_xs_331_);
v___x_339_ = lean_array_to_list(v_xs_331_);
v___x_340_ = l_Lean_Meta_mkArrayLit(v_00_u03b1_329_, v___x_339_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
if (lean_obj_tag(v___x_340_) == 0)
{
lean_object* v_a_341_; lean_object* v___x_342_; 
v_a_341_ = lean_ctor_get(v___x_340_, 0);
lean_inc(v_a_341_);
lean_dec_ref_known(v___x_340_, 1);
lean_inc_ref(v_a_325_);
v___x_342_ = l_Lean_Meta_mkEq(v_a_325_, v_a_341_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1));
v___x_345_ = l_Lean_mkRawNatLit(v_n_326_);
v___x_346_ = lean_unsigned_to_nat(3u);
v___x_347_ = lean_mk_empty_array_with_capacity(v___x_346_);
v___x_348_ = lean_array_push(v___x_347_, v_a_325_);
v___x_349_ = lean_array_push(v___x_348_, v___x_345_);
v___x_350_ = lean_array_push(v___x_349_, v_aSizeEqN_328_);
v___x_351_ = l_Lean_Meta_mkAppM(v___x_344_, v___x_350_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
if (lean_obj_tag(v___x_351_) == 0)
{
lean_object* v_a_352_; lean_object* v___x_353_; lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_a_352_ = lean_ctor_get(v___x_351_, 0);
lean_inc(v_a_352_);
lean_dec_ref_known(v___x_351_, 1);
v___x_353_ = lean_box(v___x_338_);
v___f_354_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed), 11, 5);
lean_closure_set(v___f_354_, 0, v_mvarId_324_);
lean_closure_set(v___f_354_, 1, v_xs_331_);
lean_closure_set(v___f_354_, 2, v___x_353_);
lean_closure_set(v___f_354_, 3, v_args_332_);
lean_closure_set(v___f_354_, 4, v_a_352_);
v___x_355_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3));
v___x_356_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_355_, v_a_343_, v___f_354_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
return v___x_356_;
}
else
{
lean_object* v_a_357_; lean_object* v___x_359_; uint8_t v_isShared_360_; uint8_t v_isSharedCheck_364_; 
lean_dec(v_a_343_);
lean_dec_ref(v_args_332_);
lean_dec_ref(v_xs_331_);
lean_dec(v_mvarId_324_);
v_a_357_ = lean_ctor_get(v___x_351_, 0);
v_isSharedCheck_364_ = !lean_is_exclusive(v___x_351_);
if (v_isSharedCheck_364_ == 0)
{
v___x_359_ = v___x_351_;
v_isShared_360_ = v_isSharedCheck_364_;
goto v_resetjp_358_;
}
else
{
lean_inc(v_a_357_);
lean_dec(v___x_351_);
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
lean_dec_ref(v_args_332_);
lean_dec_ref(v_xs_331_);
lean_dec_ref(v_aSizeEqN_328_);
lean_dec(v_n_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_mvarId_324_);
v_a_365_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_372_ == 0)
{
v___x_367_ = v___x_342_;
v_isShared_368_ = v_isSharedCheck_372_;
goto v_resetjp_366_;
}
else
{
lean_inc(v_a_365_);
lean_dec(v___x_342_);
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
lean_dec_ref(v_args_332_);
lean_dec_ref(v_xs_331_);
lean_dec_ref(v_aSizeEqN_328_);
lean_dec(v_n_326_);
lean_dec_ref(v_a_325_);
lean_dec(v_mvarId_324_);
v_a_373_ = lean_ctor_get(v___x_340_, 0);
v_isSharedCheck_380_ = !lean_is_exclusive(v___x_340_);
if (v_isSharedCheck_380_ == 0)
{
v___x_375_ = v___x_340_;
v_isShared_376_ = v_isSharedCheck_380_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_a_373_);
lean_dec(v___x_340_);
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
lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v___x_381_ = lean_unsigned_to_nat(1u);
v___x_382_ = lean_nat_add(v_i_330_, v___x_381_);
lean_inc(v___x_382_);
lean_inc_ref(v_00_u03b1_329_);
lean_inc(v_xNamePrefix_327_);
v___f_383_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed), 16, 10);
lean_closure_set(v___f_383_, 0, v_xs_331_);
lean_closure_set(v___f_383_, 1, v_a_325_);
lean_closure_set(v___f_383_, 2, v_i_330_);
lean_closure_set(v___f_383_, 3, v_n_326_);
lean_closure_set(v___f_383_, 4, v_aSizeEqN_328_);
lean_closure_set(v___f_383_, 5, v_args_332_);
lean_closure_set(v___f_383_, 6, v_mvarId_324_);
lean_closure_set(v___f_383_, 7, v_xNamePrefix_327_);
lean_closure_set(v___f_383_, 8, v_00_u03b1_329_);
lean_closure_set(v___f_383_, 9, v___x_382_);
v___x_384_ = lean_name_append_index_after(v_xNamePrefix_327_, v___x_382_);
v___x_385_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_384_, v_00_u03b1_329_, v___f_383_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
return v___x_385_;
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_324_ = stack[0].m_obj;
lean_object* v_a_325_ = stack[1].m_obj;
lean_object* v_n_326_ = stack[2].m_obj;
lean_object* v_xNamePrefix_327_ = stack[3].m_obj;
lean_object* v_aSizeEqN_328_ = stack[4].m_obj;
lean_object* v_00_u03b1_329_ = stack[5].m_obj;
lean_object* v_i_330_ = stack[6].m_obj;
lean_object* v_xs_331_ = stack[7].m_obj;
lean_object* v_args_332_ = stack[8].m_obj;
lean_object* v_a_333_ = stack[9].m_obj;
lean_object* v_a_334_ = stack[10].m_obj;
lean_object* v_a_335_ = stack[11].m_obj;
lean_object* v_a_336_ = stack[12].m_obj;
lean_object* v_res_386_;
v_res_386_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_324_, v_a_325_, v_n_326_, v_xNamePrefix_327_, v_aSizeEqN_328_, v_00_u03b1_329_, v_i_330_, v_xs_331_, v_args_332_, v_a_333_, v_a_334_, v_a_335_, v_a_336_);
stack->m_obj
 = v_res_386_;
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(lean_object* v_xs_387_, lean_object* v_a_388_, lean_object* v_i_389_, lean_object* v_n_390_, lean_object* v_aSizeEqN_391_, lean_object* v_args_392_, lean_object* v_mvarId_393_, lean_object* v_xNamePrefix_394_, lean_object* v_00_u03b1_395_, lean_object* v___x_396_, lean_object* v_xi_397_, lean_object* v___y_398_, lean_object* v___y_399_, lean_object* v___y_400_, lean_object* v___y_401_){
_start:
{
lean_object* v_xs_403_; lean_object* v___x_404_; 
v_xs_403_ = lean_array_push(v_xs_387_, v_xi_397_);
lean_inc_ref(v_aSizeEqN_391_);
lean_inc(v_n_390_);
lean_inc_ref(v_a_388_);
v___x_404_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_388_, v_i_389_, v_n_390_, v_aSizeEqN_391_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
if (lean_obj_tag(v___x_404_) == 0)
{
lean_object* v_a_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_a_405_ = lean_ctor_get(v___x_404_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v___x_404_, 1);
v___x_406_ = lean_array_push(v_args_392_, v_a_405_);
v___x_407_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_393_, v_a_388_, v_n_390_, v_xNamePrefix_394_, v_aSizeEqN_391_, v_00_u03b1_395_, v___x_396_, v_xs_403_, v___x_406_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
return v___x_407_;
}
else
{
lean_object* v_a_408_; lean_object* v___x_410_; uint8_t v_isShared_411_; uint8_t v_isSharedCheck_415_; 
lean_dec_ref(v_xs_403_);
lean_dec(v___x_396_);
lean_dec_ref(v_00_u03b1_395_);
lean_dec(v_xNamePrefix_394_);
lean_dec(v_mvarId_393_);
lean_dec_ref(v_args_392_);
lean_dec_ref(v_aSizeEqN_391_);
lean_dec(v_n_390_);
lean_dec_ref(v_a_388_);
v_a_408_ = lean_ctor_get(v___x_404_, 0);
v_isSharedCheck_415_ = !lean_is_exclusive(v___x_404_);
if (v_isSharedCheck_415_ == 0)
{
v___x_410_ = v___x_404_;
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
else
{
lean_inc(v_a_408_);
lean_dec(v___x_404_);
v___x_410_ = lean_box(0);
v_isShared_411_ = v_isSharedCheck_415_;
goto v_resetjp_409_;
}
v_resetjp_409_:
{
lean_object* v___x_413_; 
if (v_isShared_411_ == 0)
{
v___x_413_ = v___x_410_;
goto v_reusejp_412_;
}
else
{
lean_object* v_reuseFailAlloc_414_; 
v_reuseFailAlloc_414_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_414_, 0, v_a_408_);
v___x_413_ = v_reuseFailAlloc_414_;
goto v_reusejp_412_;
}
v_reusejp_412_:
{
return v___x_413_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_387_ = stack[0].m_obj;
lean_object* v_a_388_ = stack[1].m_obj;
lean_object* v_i_389_ = stack[2].m_obj;
lean_object* v_n_390_ = stack[3].m_obj;
lean_object* v_aSizeEqN_391_ = stack[4].m_obj;
lean_object* v_args_392_ = stack[5].m_obj;
lean_object* v_mvarId_393_ = stack[6].m_obj;
lean_object* v_xNamePrefix_394_ = stack[7].m_obj;
lean_object* v_00_u03b1_395_ = stack[8].m_obj;
lean_object* v___x_396_ = stack[9].m_obj;
lean_object* v_xi_397_ = stack[10].m_obj;
lean_object* v___y_398_ = stack[11].m_obj;
lean_object* v___y_399_ = stack[12].m_obj;
lean_object* v___y_400_ = stack[13].m_obj;
lean_object* v___y_401_ = stack[14].m_obj;
lean_object* v_res_416_;
v_res_416_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(v_xs_387_, v_a_388_, v_i_389_, v_n_390_, v_aSizeEqN_391_, v_args_392_, v_mvarId_393_, v_xNamePrefix_394_, v_00_u03b1_395_, v___x_396_, v_xi_397_, v___y_398_, v___y_399_, v___y_400_, v___y_401_);
stack->m_obj
 = v_res_416_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___boxed(lean_object* v_mvarId_417_, lean_object* v_a_418_, lean_object* v_n_419_, lean_object* v_xNamePrefix_420_, lean_object* v_aSizeEqN_421_, lean_object* v_00_u03b1_422_, lean_object* v_i_423_, lean_object* v_xs_424_, lean_object* v_args_425_, lean_object* v_a_426_, lean_object* v_a_427_, lean_object* v_a_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_417_, v_a_418_, v_n_419_, v_xNamePrefix_420_, v_aSizeEqN_421_, v_00_u03b1_422_, v_i_423_, v_xs_424_, v_args_425_, v_a_426_, v_a_427_, v_a_428_, v_a_429_);
lean_dec(v_a_429_);
lean_dec_ref(v_a_428_);
lean_dec(v_a_427_);
lean_dec_ref(v_a_426_);
return v_res_431_;
}
}
lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(lean_object* v_00_u03b1_432_, lean_object* v_name_433_, uint8_t v_bi_434_, lean_object* v_type_435_, lean_object* v_k_436_, uint8_t v_kind_437_, lean_object* v___y_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_){
_start:
{
lean_object* v___x_443_; 
v___x_443_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_433_, v_bi_434_, v_type_435_, v_k_436_, v_kind_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
return v___x_443_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_433_ = stack[1].m_obj;
uint8_t v_bi_434_ = stack[2].m_num;
lean_object* v_type_435_ = stack[3].m_obj;
lean_object* v_k_436_ = stack[4].m_obj;
uint8_t v_kind_437_ = stack[5].m_num;
lean_object* v___y_438_ = stack[6].m_obj;
lean_object* v___y_439_ = stack[7].m_obj;
lean_object* v___y_440_ = stack[8].m_obj;
lean_object* v___y_441_ = stack[9].m_obj;
lean_object* v_res_444_;
v_res_444_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(lean_box(0), v_name_433_, v_bi_434_, v_type_435_, v_k_436_, v_kind_437_, v___y_438_, v___y_439_, v___y_440_, v___y_441_);
stack->m_obj
 = v_res_444_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_445_, lean_object* v_name_446_, lean_object* v_bi_447_, lean_object* v_type_448_, lean_object* v_k_449_, lean_object* v_kind_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_, lean_object* v___y_455_){
_start:
{
uint8_t v_bi_boxed_456_; uint8_t v_kind_boxed_457_; lean_object* v_res_458_; 
v_bi_boxed_456_ = lean_unbox(v_bi_447_);
v_kind_boxed_457_ = lean_unbox(v_kind_450_);
v_res_458_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(v_00_u03b1_445_, v_name_446_, v_bi_boxed_456_, v_type_448_, v_k_449_, v_kind_boxed_457_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
lean_dec(v___y_454_);
lean_dec_ref(v___y_453_);
lean_dec(v___y_452_);
lean_dec_ref(v___y_451_);
return v_res_458_;
}
}
lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(lean_object* v_00_u03b1_459_, lean_object* v_name_460_, lean_object* v_type_461_, lean_object* v_k_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_, lean_object* v___y_466_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_460_, v_type_461_, v_k_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
return v___x_468_;
}
}
LEAN_EXPORT void l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_460_ = stack[1].m_obj;
lean_object* v_type_461_ = stack[2].m_obj;
lean_object* v_k_462_ = stack[3].m_obj;
lean_object* v___y_463_ = stack[4].m_obj;
lean_object* v___y_464_ = stack[5].m_obj;
lean_object* v___y_465_ = stack[6].m_obj;
lean_object* v___y_466_ = stack[7].m_obj;
lean_object* v_res_469_;
v_res_469_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(lean_box(0), v_name_460_, v_type_461_, v_k_462_, v___y_463_, v___y_464_, v___y_465_, v___y_466_);
stack->m_obj
 = v_res_469_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___boxed(lean_object* v_00_u03b1_470_, lean_object* v_name_471_, lean_object* v_type_472_, lean_object* v_k_473_, lean_object* v___y_474_, lean_object* v___y_475_, lean_object* v___y_476_, lean_object* v___y_477_, lean_object* v___y_478_){
_start:
{
lean_object* v_res_479_; 
v_res_479_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(v_00_u03b1_470_, v_name_471_, v_type_472_, v_k_473_, v___y_474_, v___y_475_, v___y_476_, v___y_477_);
lean_dec(v___y_477_);
lean_dec_ref(v___y_476_);
lean_dec(v___y_475_);
lean_dec_ref(v___y_474_);
return v_res_479_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_480_, lean_object* v_x_481_, lean_object* v_x_482_, lean_object* v_x_483_){
_start:
{
lean_object* v_ks_484_; lean_object* v_vs_485_; lean_object* v___x_487_; uint8_t v_isShared_488_; uint8_t v_isSharedCheck_509_; 
v_ks_484_ = lean_ctor_get(v_x_480_, 0);
v_vs_485_ = lean_ctor_get(v_x_480_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v_x_480_);
if (v_isSharedCheck_509_ == 0)
{
v___x_487_ = v_x_480_;
v_isShared_488_ = v_isSharedCheck_509_;
goto v_resetjp_486_;
}
else
{
lean_inc(v_vs_485_);
lean_inc(v_ks_484_);
lean_dec(v_x_480_);
v___x_487_ = lean_box(0);
v_isShared_488_ = v_isSharedCheck_509_;
goto v_resetjp_486_;
}
v_resetjp_486_:
{
lean_object* v___x_489_; uint8_t v___x_490_; 
v___x_489_ = lean_array_get_size(v_ks_484_);
v___x_490_ = lean_nat_dec_lt(v_x_481_, v___x_489_);
if (v___x_490_ == 0)
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
lean_dec(v_x_481_);
v___x_491_ = lean_array_push(v_ks_484_, v_x_482_);
v___x_492_ = lean_array_push(v_vs_485_, v_x_483_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_492_);
lean_ctor_set(v___x_487_, 0, v___x_491_);
v___x_494_ = v___x_487_;
goto v_reusejp_493_;
}
else
{
lean_object* v_reuseFailAlloc_495_; 
v_reuseFailAlloc_495_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_495_, 0, v___x_491_);
lean_ctor_set(v_reuseFailAlloc_495_, 1, v___x_492_);
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
lean_object* v_k_x27_496_; uint8_t v___x_497_; 
v_k_x27_496_ = lean_array_fget_borrowed(v_ks_484_, v_x_481_);
v___x_497_ = l_Lean_instBEqMVarId_beq(v_x_482_, v_k_x27_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_499_; 
if (v_isShared_488_ == 0)
{
v___x_499_ = v___x_487_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_503_; 
v_reuseFailAlloc_503_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_503_, 0, v_ks_484_);
lean_ctor_set(v_reuseFailAlloc_503_, 1, v_vs_485_);
v___x_499_ = v_reuseFailAlloc_503_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = lean_nat_add(v_x_481_, v___x_500_);
lean_dec(v_x_481_);
v_x_480_ = v___x_499_;
v_x_481_ = v___x_501_;
goto _start;
}
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_507_; 
v___x_504_ = lean_array_fset(v_ks_484_, v_x_481_, v_x_482_);
v___x_505_ = lean_array_fset(v_vs_485_, v_x_481_, v_x_483_);
lean_dec(v_x_481_);
if (v_isShared_488_ == 0)
{
lean_ctor_set(v___x_487_, 1, v___x_505_);
lean_ctor_set(v___x_487_, 0, v___x_504_);
v___x_507_ = v___x_487_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v___x_504_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v___x_505_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_510_, lean_object* v_k_511_, lean_object* v_v_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_unsigned_to_nat(0u);
v___x_514_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_510_, v___x_513_, v_k_511_, v_v_512_);
return v___x_514_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_515_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(lean_object* v_x_516_, size_t v_x_517_, size_t v_x_518_, lean_object* v_x_519_, lean_object* v_x_520_){
_start:
{
if (lean_obj_tag(v_x_516_) == 0)
{
lean_object* v_es_521_; size_t v___x_522_; size_t v___x_523_; lean_object* v_j_524_; lean_object* v___x_525_; uint8_t v___x_526_; 
v_es_521_ = lean_ctor_get(v_x_516_, 0);
v___x_522_ = ((size_t)31ULL);
v___x_523_ = lean_usize_land(v_x_517_, v___x_522_);
v_j_524_ = lean_usize_to_nat(v___x_523_);
v___x_525_ = lean_array_get_size(v_es_521_);
v___x_526_ = lean_nat_dec_lt(v_j_524_, v___x_525_);
if (v___x_526_ == 0)
{
lean_dec(v_j_524_);
lean_dec(v_x_520_);
lean_dec(v_x_519_);
return v_x_516_;
}
else
{
lean_object* v___x_528_; uint8_t v_isShared_529_; uint8_t v_isSharedCheck_565_; 
lean_inc_ref(v_es_521_);
v_isSharedCheck_565_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_565_ == 0)
{
lean_object* v_unused_566_; 
v_unused_566_ = lean_ctor_get(v_x_516_, 0);
lean_dec(v_unused_566_);
v___x_528_ = v_x_516_;
v_isShared_529_ = v_isSharedCheck_565_;
goto v_resetjp_527_;
}
else
{
lean_dec(v_x_516_);
v___x_528_ = lean_box(0);
v_isShared_529_ = v_isSharedCheck_565_;
goto v_resetjp_527_;
}
v_resetjp_527_:
{
lean_object* v_v_530_; lean_object* v___x_531_; lean_object* v_xs_x27_532_; lean_object* v___y_534_; 
v_v_530_ = lean_array_fget(v_es_521_, v_j_524_);
v___x_531_ = lean_box(0);
v_xs_x27_532_ = lean_array_fset(v_es_521_, v_j_524_, v___x_531_);
switch(lean_obj_tag(v_v_530_))
{
case 0:
{
lean_object* v_key_539_; lean_object* v_val_540_; lean_object* v___x_542_; uint8_t v_isShared_543_; uint8_t v_isSharedCheck_550_; 
v_key_539_ = lean_ctor_get(v_v_530_, 0);
v_val_540_ = lean_ctor_get(v_v_530_, 1);
v_isSharedCheck_550_ = !lean_is_exclusive(v_v_530_);
if (v_isSharedCheck_550_ == 0)
{
v___x_542_ = v_v_530_;
v_isShared_543_ = v_isSharedCheck_550_;
goto v_resetjp_541_;
}
else
{
lean_inc(v_val_540_);
lean_inc(v_key_539_);
lean_dec(v_v_530_);
v___x_542_ = lean_box(0);
v_isShared_543_ = v_isSharedCheck_550_;
goto v_resetjp_541_;
}
v_resetjp_541_:
{
uint8_t v___x_544_; 
v___x_544_ = l_Lean_instBEqMVarId_beq(v_x_519_, v_key_539_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; lean_object* v___x_546_; 
lean_del_object(v___x_542_);
v___x_545_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_539_, v_val_540_, v_x_519_, v_x_520_);
v___x_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_546_, 0, v___x_545_);
v___y_534_ = v___x_546_;
goto v___jp_533_;
}
else
{
lean_object* v___x_548_; 
lean_dec(v_val_540_);
lean_dec(v_key_539_);
if (v_isShared_543_ == 0)
{
lean_ctor_set(v___x_542_, 1, v_x_520_);
lean_ctor_set(v___x_542_, 0, v_x_519_);
v___x_548_ = v___x_542_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_x_519_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_x_520_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
v___y_534_ = v___x_548_;
goto v___jp_533_;
}
}
}
}
case 1:
{
lean_object* v_node_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_563_; 
v_node_551_ = lean_ctor_get(v_v_530_, 0);
v_isSharedCheck_563_ = !lean_is_exclusive(v_v_530_);
if (v_isSharedCheck_563_ == 0)
{
v___x_553_ = v_v_530_;
v_isShared_554_ = v_isSharedCheck_563_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_node_551_);
lean_dec(v_v_530_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_563_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
size_t v___x_555_; size_t v___x_556_; size_t v___x_557_; size_t v___x_558_; lean_object* v___x_559_; lean_object* v___x_561_; 
v___x_555_ = ((size_t)5ULL);
v___x_556_ = lean_usize_shift_right(v_x_517_, v___x_555_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_x_518_, v___x_557_);
v___x_559_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_node_551_, v___x_556_, v___x_558_, v_x_519_, v_x_520_);
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_559_);
v___x_561_ = v___x_553_;
goto v_reusejp_560_;
}
else
{
lean_object* v_reuseFailAlloc_562_; 
v_reuseFailAlloc_562_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_562_, 0, v___x_559_);
v___x_561_ = v_reuseFailAlloc_562_;
goto v_reusejp_560_;
}
v_reusejp_560_:
{
v___y_534_ = v___x_561_;
goto v___jp_533_;
}
}
}
default: 
{
lean_object* v___x_564_; 
v___x_564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_564_, 0, v_x_519_);
lean_ctor_set(v___x_564_, 1, v_x_520_);
v___y_534_ = v___x_564_;
goto v___jp_533_;
}
}
v___jp_533_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = lean_array_fset(v_xs_x27_532_, v_j_524_, v___y_534_);
lean_dec(v_j_524_);
if (v_isShared_529_ == 0)
{
lean_ctor_set(v___x_528_, 0, v___x_535_);
v___x_537_ = v___x_528_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
return v___x_537_;
}
}
}
}
}
else
{
lean_object* v_ks_567_; lean_object* v_vs_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_586_; 
v_ks_567_ = lean_ctor_get(v_x_516_, 0);
v_vs_568_ = lean_ctor_get(v_x_516_, 1);
v_isSharedCheck_586_ = !lean_is_exclusive(v_x_516_);
if (v_isSharedCheck_586_ == 0)
{
v___x_570_ = v_x_516_;
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_vs_568_);
lean_inc(v_ks_567_);
lean_dec(v_x_516_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_586_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_585_; 
v_reuseFailAlloc_585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_585_, 0, v_ks_567_);
lean_ctor_set(v_reuseFailAlloc_585_, 1, v_vs_568_);
v___x_573_ = v_reuseFailAlloc_585_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
lean_object* v_newNode_574_; size_t v___x_575_; uint8_t v___x_576_; 
v_newNode_574_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v___x_573_, v_x_519_, v_x_520_);
v___x_575_ = ((size_t)7ULL);
v___x_576_ = lean_usize_dec_le(v___x_575_, v_x_518_);
if (v___x_576_ == 0)
{
lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; 
v___x_577_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_574_);
v___x_578_ = lean_unsigned_to_nat(4u);
v___x_579_ = lean_nat_dec_lt(v___x_577_, v___x_578_);
lean_dec(v___x_577_);
if (v___x_579_ == 0)
{
lean_object* v_ks_580_; lean_object* v_vs_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v_ks_580_ = lean_ctor_get(v_newNode_574_, 0);
lean_inc_ref(v_ks_580_);
v_vs_581_ = lean_ctor_get(v_newNode_574_, 1);
lean_inc_ref(v_vs_581_);
lean_dec_ref(v_newNode_574_);
v___x_582_ = lean_unsigned_to_nat(0u);
v___x_583_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_584_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_x_518_, v_ks_580_, v_vs_581_, v___x_582_, v___x_583_);
lean_dec_ref(v_vs_581_);
lean_dec_ref(v_ks_580_);
return v___x_584_;
}
else
{
return v_newNode_574_;
}
}
else
{
return v_newNode_574_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_516_ = stack[0].m_obj;
size_t v_x_517_ = stack[1].m_num;
size_t v_x_518_ = stack[2].m_num;
lean_object* v_x_519_ = stack[3].m_obj;
lean_object* v_x_520_ = stack[4].m_obj;
lean_object* v_res_587_;
v_res_587_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_516_, v_x_517_, v_x_518_, v_x_519_, v_x_520_);
stack->m_obj
 = v_res_587_;
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_588_, lean_object* v_keys_589_, lean_object* v_vals_590_, lean_object* v_i_591_, lean_object* v_entries_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = lean_array_get_size(v_keys_589_);
v___x_594_ = lean_nat_dec_lt(v_i_591_, v___x_593_);
if (v___x_594_ == 0)
{
lean_dec(v_i_591_);
return v_entries_592_;
}
else
{
lean_object* v_k_595_; lean_object* v_v_596_; uint64_t v___x_597_; size_t v_h_598_; size_t v___x_599_; lean_object* v___x_600_; size_t v___x_601_; size_t v___x_602_; size_t v___x_603_; size_t v_h_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v_k_595_ = lean_array_fget_borrowed(v_keys_589_, v_i_591_);
v_v_596_ = lean_array_fget_borrowed(v_vals_590_, v_i_591_);
v___x_597_ = l_Lean_instHashableMVarId_hash(v_k_595_);
v_h_598_ = lean_uint64_to_usize(v___x_597_);
v___x_599_ = ((size_t)5ULL);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = ((size_t)1ULL);
v___x_602_ = lean_usize_sub(v_depth_588_, v___x_601_);
v___x_603_ = lean_usize_mul(v___x_599_, v___x_602_);
v_h_604_ = lean_usize_shift_right(v_h_598_, v___x_603_);
v___x_605_ = lean_nat_add(v_i_591_, v___x_600_);
lean_dec(v_i_591_);
lean_inc(v_v_596_);
lean_inc(v_k_595_);
v___x_606_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_entries_592_, v_h_604_, v_depth_588_, v_k_595_, v_v_596_);
v_i_591_ = v___x_605_;
v_entries_592_ = v___x_606_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
size_t v_depth_588_ = stack[0].m_num;
lean_object* v_keys_589_ = stack[1].m_obj;
lean_object* v_vals_590_ = stack[2].m_obj;
lean_object* v_i_591_ = stack[3].m_obj;
lean_object* v_entries_592_ = stack[4].m_obj;
lean_object* v_res_608_;
v_res_608_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_588_, v_keys_589_, v_vals_590_, v_i_591_, v_entries_592_);
stack->m_obj
 = v_res_608_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_609_, lean_object* v_keys_610_, lean_object* v_vals_611_, lean_object* v_i_612_, lean_object* v_entries_613_){
_start:
{
size_t v_depth_boxed_614_; lean_object* v_res_615_; 
v_depth_boxed_614_ = lean_unbox_usize(v_depth_609_);
lean_dec(v_depth_609_);
v_res_615_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_614_, v_keys_610_, v_vals_611_, v_i_612_, v_entries_613_);
lean_dec_ref(v_vals_611_);
lean_dec_ref(v_keys_610_);
return v_res_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_616_, lean_object* v_x_617_, lean_object* v_x_618_, lean_object* v_x_619_, lean_object* v_x_620_){
_start:
{
size_t v_x_1030__boxed_621_; size_t v_x_1031__boxed_622_; lean_object* v_res_623_; 
v_x_1030__boxed_621_ = lean_unbox_usize(v_x_617_);
lean_dec(v_x_617_);
v_x_1031__boxed_622_ = lean_unbox_usize(v_x_618_);
lean_dec(v_x_618_);
v_res_623_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_616_, v_x_1030__boxed_621_, v_x_1031__boxed_622_, v_x_619_, v_x_620_);
return v_res_623_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(lean_object* v_x_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
uint64_t v___x_627_; size_t v___x_628_; size_t v___x_629_; lean_object* v___x_630_; 
v___x_627_ = l_Lean_instHashableMVarId_hash(v_x_625_);
v___x_628_ = lean_uint64_to_usize(v___x_627_);
v___x_629_ = ((size_t)1ULL);
v___x_630_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_624_, v___x_628_, v___x_629_, v_x_625_, v_x_626_);
return v___x_630_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(lean_object* v_mvarId_631_, lean_object* v_val_632_, lean_object* v___y_633_){
_start:
{
lean_object* v___x_635_; lean_object* v_mctx_636_; lean_object* v_cache_637_; lean_object* v_zetaDeltaFVarIds_638_; lean_object* v_postponed_639_; lean_object* v_diag_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_670_; 
v___x_635_ = lean_st_ref_take(v___y_633_);
v_mctx_636_ = lean_ctor_get(v___x_635_, 0);
v_cache_637_ = lean_ctor_get(v___x_635_, 1);
v_zetaDeltaFVarIds_638_ = lean_ctor_get(v___x_635_, 2);
v_postponed_639_ = lean_ctor_get(v___x_635_, 3);
v_diag_640_ = lean_ctor_get(v___x_635_, 4);
v_isSharedCheck_670_ = !lean_is_exclusive(v___x_635_);
if (v_isSharedCheck_670_ == 0)
{
v___x_642_ = v___x_635_;
v_isShared_643_ = v_isSharedCheck_670_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_diag_640_);
lean_inc(v_postponed_639_);
lean_inc(v_zetaDeltaFVarIds_638_);
lean_inc(v_cache_637_);
lean_inc(v_mctx_636_);
lean_dec(v___x_635_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_670_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v_depth_644_; lean_object* v_levelAssignDepth_645_; lean_object* v_lmvarCounter_646_; lean_object* v_mvarCounter_647_; lean_object* v_lDecls_648_; lean_object* v_decls_649_; lean_object* v_userNames_650_; lean_object* v_lAssignment_651_; lean_object* v_eAssignment_652_; lean_object* v_dAssignment_653_; lean_object* v_instanceTypedMVars_654_; lean_object* v_synthNormMemo_655_; lean_object* v___x_657_; uint8_t v_isShared_658_; uint8_t v_isSharedCheck_669_; 
v_depth_644_ = lean_ctor_get(v_mctx_636_, 0);
v_levelAssignDepth_645_ = lean_ctor_get(v_mctx_636_, 1);
v_lmvarCounter_646_ = lean_ctor_get(v_mctx_636_, 2);
v_mvarCounter_647_ = lean_ctor_get(v_mctx_636_, 3);
v_lDecls_648_ = lean_ctor_get(v_mctx_636_, 4);
v_decls_649_ = lean_ctor_get(v_mctx_636_, 5);
v_userNames_650_ = lean_ctor_get(v_mctx_636_, 6);
v_lAssignment_651_ = lean_ctor_get(v_mctx_636_, 7);
v_eAssignment_652_ = lean_ctor_get(v_mctx_636_, 8);
v_dAssignment_653_ = lean_ctor_get(v_mctx_636_, 9);
v_instanceTypedMVars_654_ = lean_ctor_get(v_mctx_636_, 10);
v_synthNormMemo_655_ = lean_ctor_get(v_mctx_636_, 11);
v_isSharedCheck_669_ = !lean_is_exclusive(v_mctx_636_);
if (v_isSharedCheck_669_ == 0)
{
v___x_657_ = v_mctx_636_;
v_isShared_658_ = v_isSharedCheck_669_;
goto v_resetjp_656_;
}
else
{
lean_inc(v_synthNormMemo_655_);
lean_inc(v_instanceTypedMVars_654_);
lean_inc(v_dAssignment_653_);
lean_inc(v_eAssignment_652_);
lean_inc(v_lAssignment_651_);
lean_inc(v_userNames_650_);
lean_inc(v_decls_649_);
lean_inc(v_lDecls_648_);
lean_inc(v_mvarCounter_647_);
lean_inc(v_lmvarCounter_646_);
lean_inc(v_levelAssignDepth_645_);
lean_inc(v_depth_644_);
lean_dec(v_mctx_636_);
v___x_657_ = lean_box(0);
v_isShared_658_ = v_isSharedCheck_669_;
goto v_resetjp_656_;
}
v_resetjp_656_:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_662_; 
v___x_659_ = lean_box(0);
v___x_660_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_eAssignment_652_, v_mvarId_631_, v_val_632_);
if (v_isShared_658_ == 0)
{
lean_ctor_set(v___x_657_, 8, v___x_660_);
v___x_662_ = v___x_657_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_668_; 
v_reuseFailAlloc_668_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_668_, 0, v_depth_644_);
lean_ctor_set(v_reuseFailAlloc_668_, 1, v_levelAssignDepth_645_);
lean_ctor_set(v_reuseFailAlloc_668_, 2, v_lmvarCounter_646_);
lean_ctor_set(v_reuseFailAlloc_668_, 3, v_mvarCounter_647_);
lean_ctor_set(v_reuseFailAlloc_668_, 4, v_lDecls_648_);
lean_ctor_set(v_reuseFailAlloc_668_, 5, v_decls_649_);
lean_ctor_set(v_reuseFailAlloc_668_, 6, v_userNames_650_);
lean_ctor_set(v_reuseFailAlloc_668_, 7, v_lAssignment_651_);
lean_ctor_set(v_reuseFailAlloc_668_, 8, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_668_, 9, v_dAssignment_653_);
lean_ctor_set(v_reuseFailAlloc_668_, 10, v_instanceTypedMVars_654_);
lean_ctor_set(v_reuseFailAlloc_668_, 11, v_synthNormMemo_655_);
v___x_662_ = v_reuseFailAlloc_668_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
lean_object* v___x_664_; 
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 0, v___x_662_);
v___x_664_ = v___x_642_;
goto v_reusejp_663_;
}
else
{
lean_object* v_reuseFailAlloc_667_; 
v_reuseFailAlloc_667_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_667_, 0, v___x_662_);
lean_ctor_set(v_reuseFailAlloc_667_, 1, v_cache_637_);
lean_ctor_set(v_reuseFailAlloc_667_, 2, v_zetaDeltaFVarIds_638_);
lean_ctor_set(v_reuseFailAlloc_667_, 3, v_postponed_639_);
lean_ctor_set(v_reuseFailAlloc_667_, 4, v_diag_640_);
v___x_664_ = v_reuseFailAlloc_667_;
goto v_reusejp_663_;
}
v_reusejp_663_:
{
lean_object* v___x_665_; lean_object* v___x_666_; 
v___x_665_ = lean_st_ref_put(v___y_633_, v___x_664_);
v___x_666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_666_, 0, v___x_659_);
return v___x_666_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_631_ = stack[0].m_obj;
lean_object* v_val_632_ = stack[1].m_obj;
lean_object* v___y_633_ = stack[2].m_obj;
lean_object* v_res_671_;
v_res_671_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_631_, v_val_632_, v___y_633_);
stack->m_obj
 = v_res_671_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg___boxed(lean_object* v_mvarId_672_, lean_object* v_val_673_, lean_object* v___y_674_, lean_object* v___y_675_){
_start:
{
lean_object* v_res_676_; 
v_res_676_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_672_, v_val_673_, v___y_674_);
lean_dec(v___y_674_);
return v_res_676_;
}
}
lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object* v_mvarId_679_, lean_object* v_a_680_, lean_object* v_n_681_, lean_object* v_xNamePrefix_682_, lean_object* v_aSizeEqN_683_, lean_object* v_a_684_, lean_object* v_a_685_, lean_object* v_a_686_, lean_object* v_a_687_){
_start:
{
lean_object* v___x_689_; 
lean_inc_ref(v_a_680_);
v___x_689_ = l_Lean_Meta_getArrayArgType(v_a_680_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_object* v_a_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; 
v_a_690_ = lean_ctor_get(v___x_689_, 0);
lean_inc(v_a_690_);
lean_dec_ref_known(v___x_689_, 1);
v___x_691_ = lean_unsigned_to_nat(0u);
v___x_692_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0));
lean_inc(v_mvarId_679_);
v___x_693_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_679_, v_a_680_, v_n_681_, v_xNamePrefix_682_, v_aSizeEqN_683_, v_a_690_, v___x_691_, v___x_692_, v___x_692_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_693_) == 0)
{
lean_object* v_a_694_; lean_object* v_fst_695_; lean_object* v_snd_696_; lean_object* v___x_697_; 
v_a_694_ = lean_ctor_get(v___x_693_, 0);
lean_inc(v_a_694_);
lean_dec_ref_known(v___x_693_, 1);
v_fst_695_ = lean_ctor_get(v_a_694_, 0);
lean_inc(v_fst_695_);
v_snd_696_ = lean_ctor_get(v_a_694_, 1);
lean_inc(v_snd_696_);
lean_dec(v_a_694_);
lean_inc(v_mvarId_679_);
v___x_697_ = l_Lean_MVarId_getTag(v_mvarId_679_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v_a_698_; lean_object* v___x_699_; 
v_a_698_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_a_698_);
lean_dec_ref_known(v___x_697_, 1);
v___x_699_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_695_, v_a_698_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
if (lean_obj_tag(v___x_699_) == 0)
{
lean_object* v_a_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_704_; uint8_t v_isShared_705_; uint8_t v_isSharedCheck_710_; 
v_a_700_ = lean_ctor_get(v___x_699_, 0);
lean_inc_n(v_a_700_, 2);
lean_dec_ref_known(v___x_699_, 1);
v___x_701_ = l_Lean_mkAppN(v_a_700_, v_snd_696_);
lean_dec(v_snd_696_);
v___x_702_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_679_, v___x_701_, v_a_685_);
v_isSharedCheck_710_ = !lean_is_exclusive(v___x_702_);
if (v_isSharedCheck_710_ == 0)
{
lean_object* v_unused_711_; 
v_unused_711_ = lean_ctor_get(v___x_702_, 0);
lean_dec(v_unused_711_);
v___x_704_ = v___x_702_;
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
else
{
lean_dec(v___x_702_);
v___x_704_ = lean_box(0);
v_isShared_705_ = v_isSharedCheck_710_;
goto v_resetjp_703_;
}
v_resetjp_703_:
{
lean_object* v___x_706_; lean_object* v___x_708_; 
v___x_706_ = l_Lean_Expr_mvarId_x21(v_a_700_);
lean_dec(v_a_700_);
if (v_isShared_705_ == 0)
{
lean_ctor_set(v___x_704_, 0, v___x_706_);
v___x_708_ = v___x_704_;
goto v_reusejp_707_;
}
else
{
lean_object* v_reuseFailAlloc_709_; 
v_reuseFailAlloc_709_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_709_, 0, v___x_706_);
v___x_708_ = v_reuseFailAlloc_709_;
goto v_reusejp_707_;
}
v_reusejp_707_:
{
return v___x_708_;
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_snd_696_);
lean_dec(v_mvarId_679_);
v_a_712_ = lean_ctor_get(v___x_699_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_699_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_699_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_699_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_717_; 
if (v_isShared_715_ == 0)
{
v___x_717_ = v___x_714_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_a_712_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
return v___x_717_;
}
}
}
}
else
{
lean_object* v_a_720_; lean_object* v___x_722_; uint8_t v_isShared_723_; uint8_t v_isSharedCheck_727_; 
lean_dec(v_snd_696_);
lean_dec(v_fst_695_);
lean_dec(v_mvarId_679_);
v_a_720_ = lean_ctor_get(v___x_697_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_697_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_697_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_697_);
v___x_722_ = lean_box(0);
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
v_resetjp_721_:
{
lean_object* v___x_725_; 
if (v_isShared_723_ == 0)
{
v___x_725_ = v___x_722_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_a_720_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
return v___x_725_;
}
}
}
}
else
{
lean_object* v_a_728_; lean_object* v___x_730_; uint8_t v_isShared_731_; uint8_t v_isSharedCheck_735_; 
lean_dec(v_mvarId_679_);
v_a_728_ = lean_ctor_get(v___x_693_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v___x_693_);
if (v_isSharedCheck_735_ == 0)
{
v___x_730_ = v___x_693_;
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
else
{
lean_inc(v_a_728_);
lean_dec(v___x_693_);
v___x_730_ = lean_box(0);
v_isShared_731_ = v_isSharedCheck_735_;
goto v_resetjp_729_;
}
v_resetjp_729_:
{
lean_object* v___x_733_; 
if (v_isShared_731_ == 0)
{
v___x_733_ = v___x_730_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_a_728_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
else
{
lean_object* v_a_736_; lean_object* v___x_738_; uint8_t v_isShared_739_; uint8_t v_isSharedCheck_743_; 
lean_dec_ref(v_aSizeEqN_683_);
lean_dec(v_xNamePrefix_682_);
lean_dec(v_n_681_);
lean_dec_ref(v_a_680_);
lean_dec(v_mvarId_679_);
v_a_736_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_743_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_743_ == 0)
{
v___x_738_ = v___x_689_;
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
else
{
lean_inc(v_a_736_);
lean_dec(v___x_689_);
v___x_738_ = lean_box(0);
v_isShared_739_ = v_isSharedCheck_743_;
goto v_resetjp_737_;
}
v_resetjp_737_:
{
lean_object* v___x_741_; 
if (v_isShared_739_ == 0)
{
v___x_741_ = v___x_738_;
goto v_reusejp_740_;
}
else
{
lean_object* v_reuseFailAlloc_742_; 
v_reuseFailAlloc_742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_742_, 0, v_a_736_);
v___x_741_ = v_reuseFailAlloc_742_;
goto v_reusejp_740_;
}
v_reusejp_740_:
{
return v___x_741_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_679_ = stack[0].m_obj;
lean_object* v_a_680_ = stack[1].m_obj;
lean_object* v_n_681_ = stack[2].m_obj;
lean_object* v_xNamePrefix_682_ = stack[3].m_obj;
lean_object* v_aSizeEqN_683_ = stack[4].m_obj;
lean_object* v_a_684_ = stack[5].m_obj;
lean_object* v_a_685_ = stack[6].m_obj;
lean_object* v_a_686_ = stack[7].m_obj;
lean_object* v_a_687_ = stack[8].m_obj;
lean_object* v_res_744_;
v_res_744_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_679_, v_a_680_, v_n_681_, v_xNamePrefix_682_, v_aSizeEqN_683_, v_a_684_, v_a_685_, v_a_686_, v_a_687_);
stack->m_obj
 = v_res_744_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___boxed(lean_object* v_mvarId_745_, lean_object* v_a_746_, lean_object* v_n_747_, lean_object* v_xNamePrefix_748_, lean_object* v_aSizeEqN_749_, lean_object* v_a_750_, lean_object* v_a_751_, lean_object* v_a_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
lean_object* v_res_755_; 
v_res_755_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_745_, v_a_746_, v_n_747_, v_xNamePrefix_748_, v_aSizeEqN_749_, v_a_750_, v_a_751_, v_a_752_, v_a_753_);
lean_dec(v_a_753_);
lean_dec_ref(v_a_752_);
lean_dec(v_a_751_);
lean_dec_ref(v_a_750_);
return v_res_755_;
}
}
lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(lean_object* v_mvarId_756_, lean_object* v_val_757_, lean_object* v___y_758_, lean_object* v___y_759_, lean_object* v___y_760_, lean_object* v___y_761_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_756_, v_val_757_, v___y_759_);
return v___x_763_;
}
}
LEAN_EXPORT void l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_756_ = stack[0].m_obj;
lean_object* v_val_757_ = stack[1].m_obj;
lean_object* v___y_758_ = stack[2].m_obj;
lean_object* v___y_759_ = stack[3].m_obj;
lean_object* v___y_760_ = stack[4].m_obj;
lean_object* v___y_761_ = stack[5].m_obj;
lean_object* v_res_764_;
v_res_764_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(v_mvarId_756_, v_val_757_, v___y_758_, v___y_759_, v___y_760_, v___y_761_);
stack->m_obj
 = v_res_764_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___boxed(lean_object* v_mvarId_765_, lean_object* v_val_766_, lean_object* v___y_767_, lean_object* v___y_768_, lean_object* v___y_769_, lean_object* v___y_770_, lean_object* v___y_771_){
_start:
{
lean_object* v_res_772_; 
v_res_772_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(v_mvarId_765_, v_val_766_, v___y_767_, v___y_768_, v___y_769_, v___y_770_);
lean_dec(v___y_770_);
lean_dec_ref(v___y_769_);
lean_dec(v___y_768_);
lean_dec_ref(v___y_767_);
return v_res_772_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0(lean_object* v_00_u03b2_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_x_774_, v_x_775_, v_x_776_);
return v___x_777_;
}
}
lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_778_, lean_object* v_x_779_, size_t v_x_780_, size_t v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_779_, v_x_780_, v_x_781_, v_x_782_, v_x_783_);
return v___x_784_;
}
}
LEAN_EXPORT void l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_779_ = stack[1].m_obj;
size_t v_x_780_ = stack[2].m_num;
size_t v_x_781_ = stack[3].m_num;
lean_object* v_x_782_ = stack[4].m_obj;
lean_object* v_x_783_ = stack[5].m_obj;
lean_object* v_res_785_;
v_res_785_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(lean_box(0), v_x_779_, v_x_780_, v_x_781_, v_x_782_, v_x_783_);
stack->m_obj
 = v_res_785_;
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_786_, lean_object* v_x_787_, lean_object* v_x_788_, lean_object* v_x_789_, lean_object* v_x_790_, lean_object* v_x_791_){
_start:
{
size_t v_x_1574__boxed_792_; size_t v_x_1575__boxed_793_; lean_object* v_res_794_; 
v_x_1574__boxed_792_ = lean_unbox_usize(v_x_788_);
lean_dec(v_x_788_);
v_x_1575__boxed_793_ = lean_unbox_usize(v_x_789_);
lean_dec(v_x_789_);
v_res_794_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(v_00_u03b2_786_, v_x_787_, v_x_1574__boxed_792_, v_x_1575__boxed_793_, v_x_790_, v_x_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_795_, lean_object* v_n_796_, lean_object* v_k_797_, lean_object* v_v_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v_n_796_, v_k_797_, v_v_798_);
return v___x_799_;
}
}
lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_800_, size_t v_depth_801_, lean_object* v_keys_802_, lean_object* v_vals_803_, lean_object* v_heq_804_, lean_object* v_i_805_, lean_object* v_entries_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_801_, v_keys_802_, v_vals_803_, v_i_805_, v_entries_806_);
return v___x_807_;
}
}
LEAN_EXPORT void l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3_0interp(lean_interpreter_value* stack)
{
size_t v_depth_801_ = stack[1].m_num;
lean_object* v_keys_802_ = stack[2].m_obj;
lean_object* v_vals_803_ = stack[3].m_obj;
lean_object* v_i_805_ = stack[5].m_obj;
lean_object* v_entries_806_ = stack[6].m_obj;
lean_object* v_res_808_;
v_res_808_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(lean_box(0), v_depth_801_, v_keys_802_, v_vals_803_, lean_box(0), v_i_805_, v_entries_806_);
stack->m_obj
 = v_res_808_;
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_809_, lean_object* v_depth_810_, lean_object* v_keys_811_, lean_object* v_vals_812_, lean_object* v_heq_813_, lean_object* v_i_814_, lean_object* v_entries_815_){
_start:
{
size_t v_depth_boxed_816_; lean_object* v_res_817_; 
v_depth_boxed_816_ = lean_unbox_usize(v_depth_810_);
lean_dec(v_depth_810_);
v_res_817_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_809_, v_depth_boxed_816_, v_keys_811_, v_vals_812_, v_heq_813_, v_i_814_, v_entries_815_);
lean_dec_ref(v_vals_812_);
lean_dec_ref(v_keys_811_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_818_, lean_object* v_x_819_, lean_object* v_x_820_, lean_object* v_x_821_, lean_object* v_x_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_819_, v_x_820_, v_x_821_, v_x_822_);
return v___x_823_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(lean_object* v_mvarId_824_, lean_object* v_x_825_, lean_object* v___y_826_, lean_object* v___y_827_, lean_object* v___y_828_, lean_object* v___y_829_){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_824_, v_x_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
if (lean_obj_tag(v___x_831_) == 0)
{
lean_object* v_a_832_; lean_object* v___x_834_; uint8_t v_isShared_835_; uint8_t v_isSharedCheck_839_; 
v_a_832_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_839_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_839_ == 0)
{
v___x_834_ = v___x_831_;
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
else
{
lean_inc(v_a_832_);
lean_dec(v___x_831_);
v___x_834_ = lean_box(0);
v_isShared_835_ = v_isSharedCheck_839_;
goto v_resetjp_833_;
}
v_resetjp_833_:
{
lean_object* v___x_837_; 
if (v_isShared_835_ == 0)
{
v___x_837_ = v___x_834_;
goto v_reusejp_836_;
}
else
{
lean_object* v_reuseFailAlloc_838_; 
v_reuseFailAlloc_838_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_838_, 0, v_a_832_);
v___x_837_ = v_reuseFailAlloc_838_;
goto v_reusejp_836_;
}
v_reusejp_836_:
{
return v___x_837_;
}
}
}
else
{
lean_object* v_a_840_; lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_847_; 
v_a_840_ = lean_ctor_get(v___x_831_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_831_);
if (v_isSharedCheck_847_ == 0)
{
v___x_842_ = v___x_831_;
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
else
{
lean_inc(v_a_840_);
lean_dec(v___x_831_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_847_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_845_; 
if (v_isShared_843_ == 0)
{
v___x_845_ = v___x_842_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_a_840_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_824_ = stack[0].m_obj;
lean_object* v_x_825_ = stack[1].m_obj;
lean_object* v___y_826_ = stack[2].m_obj;
lean_object* v___y_827_ = stack[3].m_obj;
lean_object* v___y_828_ = stack[4].m_obj;
lean_object* v___y_829_ = stack[5].m_obj;
lean_object* v_res_848_;
v_res_848_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_824_, v_x_825_, v___y_826_, v___y_827_, v___y_828_, v___y_829_);
stack->m_obj
 = v_res_848_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg___boxed(lean_object* v_mvarId_849_, lean_object* v_x_850_, lean_object* v___y_851_, lean_object* v___y_852_, lean_object* v___y_853_, lean_object* v___y_854_, lean_object* v___y_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_849_, v_x_850_, v___y_851_, v___y_852_, v___y_853_, v___y_854_);
lean_dec(v___y_854_);
lean_dec_ref(v___y_853_);
lean_dec(v___y_852_);
lean_dec_ref(v___y_851_);
return v_res_856_;
}
}
lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(lean_object* v_00_u03b1_857_, lean_object* v_mvarId_858_, lean_object* v_x_859_, lean_object* v___y_860_, lean_object* v___y_861_, lean_object* v___y_862_, lean_object* v___y_863_){
_start:
{
lean_object* v___x_865_; 
v___x_865_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_858_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
return v___x_865_;
}
}
LEAN_EXPORT void l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_858_ = stack[1].m_obj;
lean_object* v_x_859_ = stack[2].m_obj;
lean_object* v___y_860_ = stack[3].m_obj;
lean_object* v___y_861_ = stack[4].m_obj;
lean_object* v___y_862_ = stack[5].m_obj;
lean_object* v___y_863_ = stack[6].m_obj;
lean_object* v_res_866_;
v_res_866_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(lean_box(0), v_mvarId_858_, v_x_859_, v___y_860_, v___y_861_, v___y_862_, v___y_863_);
stack->m_obj
 = v_res_866_;
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___boxed(lean_object* v_00_u03b1_867_, lean_object* v_mvarId_868_, lean_object* v_x_869_, lean_object* v___y_870_, lean_object* v___y_871_, lean_object* v___y_872_, lean_object* v___y_873_, lean_object* v___y_874_){
_start:
{
lean_object* v_res_875_; 
v_res_875_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(v_00_u03b1_867_, v_mvarId_868_, v_x_869_, v___y_870_, v___y_871_, v___y_872_, v___y_873_);
lean_dec(v___y_873_);
lean_dec_ref(v___y_872_);
lean_dec(v___y_871_);
lean_dec_ref(v___y_870_);
return v_res_875_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(size_t v_sz_876_, size_t v_i_877_, lean_object* v_bs_878_){
_start:
{
uint8_t v___x_879_; 
v___x_879_ = lean_usize_dec_lt(v_i_877_, v_sz_876_);
if (v___x_879_ == 0)
{
return v_bs_878_;
}
else
{
lean_object* v_v_880_; lean_object* v___x_881_; lean_object* v_bs_x27_882_; lean_object* v___x_883_; size_t v___x_884_; size_t v___x_885_; lean_object* v___x_886_; 
v_v_880_ = lean_array_uget(v_bs_878_, v_i_877_);
v___x_881_ = lean_unsigned_to_nat(0u);
v_bs_x27_882_ = lean_array_uset(v_bs_878_, v_i_877_, v___x_881_);
v___x_883_ = l_Lean_mkRawNatLit(v_v_880_);
v___x_884_ = ((size_t)1ULL);
v___x_885_ = lean_usize_add(v_i_877_, v___x_884_);
v___x_886_ = lean_array_uset(v_bs_x27_882_, v_i_877_, v___x_883_);
v_i_877_ = v___x_885_;
v_bs_878_ = v___x_886_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_876_ = stack[0].m_num;
size_t v_i_877_ = stack[1].m_num;
lean_object* v_bs_878_ = stack[2].m_obj;
lean_object* v_res_888_;
v_res_888_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_876_, v_i_877_, v_bs_878_);
stack->m_obj
 = v_res_888_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0___boxed(lean_object* v_sz_889_, lean_object* v_i_890_, lean_object* v_bs_891_){
_start:
{
size_t v_sz_boxed_892_; size_t v_i_boxed_893_; lean_object* v_res_894_; 
v_sz_boxed_892_ = lean_unbox_usize(v_sz_889_);
lean_dec(v_sz_889_);
v_i_boxed_893_ = lean_unbox_usize(v_i_890_);
lean_dec(v_i_890_);
v_res_894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_boxed_892_, v_i_boxed_893_, v_bs_891_);
return v_res_894_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(lean_object* v___x_895_, lean_object* v_mvarId_896_, lean_object* v_a_897_, lean_object* v___x_898_, lean_object* v_xNamePrefix_899_, lean_object* v___x_900_, lean_object* v_subst_901_, uint8_t v___x_902_, lean_object* v___y_903_, lean_object* v___y_904_, lean_object* v___y_905_, lean_object* v___y_906_){
_start:
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Meta_mkEqSymm(v___x_895_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_908_) == 0)
{
lean_object* v_a_909_; lean_object* v___x_910_; 
v_a_909_ = lean_ctor_get(v___x_908_, 0);
lean_inc(v_a_909_);
lean_dec_ref_known(v___x_908_, 1);
lean_inc(v___x_898_);
v___x_910_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_896_, v_a_897_, v___x_898_, v_xNamePrefix_899_, v_a_909_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_910_) == 0)
{
lean_object* v_a_911_; lean_object* v___x_912_; uint8_t v___x_913_; lean_object* v___x_914_; 
v_a_911_ = lean_ctor_get(v___x_910_, 0);
lean_inc(v_a_911_);
lean_dec_ref_known(v___x_910_, 1);
v___x_912_ = lean_box(0);
v___x_913_ = 0;
v___x_914_ = l_Lean_Meta_introNCore(v_a_911_, v___x_898_, v___x_912_, v___x_913_, v___x_913_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_914_) == 0)
{
lean_object* v_a_915_; lean_object* v_fst_916_; lean_object* v_snd_917_; lean_object* v___x_918_; 
v_a_915_ = lean_ctor_get(v___x_914_, 0);
lean_inc(v_a_915_);
lean_dec_ref_known(v___x_914_, 1);
v_fst_916_ = lean_ctor_get(v_a_915_, 0);
lean_inc(v_fst_916_);
v_snd_917_ = lean_ctor_get(v_a_915_, 1);
lean_inc(v_snd_917_);
lean_dec(v_a_915_);
v___x_918_ = l_Lean_Meta_intro1Core(v_snd_917_, v___x_913_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_918_) == 0)
{
lean_object* v_a_919_; lean_object* v_fst_920_; lean_object* v_snd_921_; lean_object* v___x_922_; 
v_a_919_ = lean_ctor_get(v___x_918_, 0);
lean_inc(v_a_919_);
lean_dec_ref_known(v___x_918_, 1);
v_fst_920_ = lean_ctor_get(v_a_919_, 0);
lean_inc(v_fst_920_);
v_snd_921_ = lean_ctor_get(v_a_919_, 1);
lean_inc(v_snd_921_);
lean_dec(v_a_919_);
v___x_922_ = l_Lean_MVarId_clear(v_snd_921_, v___x_900_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_922_) == 0)
{
lean_object* v_a_923_; lean_object* v___x_924_; 
v_a_923_ = lean_ctor_get(v___x_922_, 0);
lean_inc(v_a_923_);
lean_dec_ref_known(v___x_922_, 1);
v___x_924_ = l_Lean_Meta_substCore(v_a_923_, v_fst_920_, v___x_913_, v_subst_901_, v___x_902_, v___x_913_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
if (lean_obj_tag(v___x_924_) == 0)
{
lean_object* v_a_925_; lean_object* v___x_927_; uint8_t v_isShared_928_; uint8_t v_isSharedCheck_936_; 
v_a_925_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_936_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_936_ == 0)
{
v___x_927_ = v___x_924_;
v_isShared_928_ = v_isSharedCheck_936_;
goto v_resetjp_926_;
}
else
{
lean_inc(v_a_925_);
lean_dec(v___x_924_);
v___x_927_ = lean_box(0);
v_isShared_928_ = v_isSharedCheck_936_;
goto v_resetjp_926_;
}
v_resetjp_926_:
{
lean_object* v_fst_929_; lean_object* v_snd_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_934_; 
v_fst_929_ = lean_ctor_get(v_a_925_, 0);
lean_inc(v_fst_929_);
v_snd_930_ = lean_ctor_get(v_a_925_, 1);
lean_inc(v_snd_930_);
lean_dec(v_a_925_);
v___x_931_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0));
v___x_932_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_932_, 0, v_snd_930_);
lean_ctor_set(v___x_932_, 1, v_fst_916_);
lean_ctor_set(v___x_932_, 2, v___x_931_);
lean_ctor_set(v___x_932_, 3, v_fst_929_);
if (v_isShared_928_ == 0)
{
lean_ctor_set(v___x_927_, 0, v___x_932_);
v___x_934_ = v___x_927_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
else
{
lean_object* v_a_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_944_; 
lean_dec(v_fst_916_);
v_a_937_ = lean_ctor_get(v___x_924_, 0);
v_isSharedCheck_944_ = !lean_is_exclusive(v___x_924_);
if (v_isSharedCheck_944_ == 0)
{
v___x_939_ = v___x_924_;
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_a_937_);
lean_dec(v___x_924_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_944_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_942_; 
if (v_isShared_940_ == 0)
{
v___x_942_ = v___x_939_;
goto v_reusejp_941_;
}
else
{
lean_object* v_reuseFailAlloc_943_; 
v_reuseFailAlloc_943_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_943_, 0, v_a_937_);
v___x_942_ = v_reuseFailAlloc_943_;
goto v_reusejp_941_;
}
v_reusejp_941_:
{
return v___x_942_;
}
}
}
}
else
{
lean_object* v_a_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_952_; 
lean_dec(v_fst_920_);
lean_dec(v_fst_916_);
lean_dec(v_subst_901_);
v_a_945_ = lean_ctor_get(v___x_922_, 0);
v_isSharedCheck_952_ = !lean_is_exclusive(v___x_922_);
if (v_isSharedCheck_952_ == 0)
{
v___x_947_ = v___x_922_;
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_a_945_);
lean_dec(v___x_922_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_952_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_950_; 
if (v_isShared_948_ == 0)
{
v___x_950_ = v___x_947_;
goto v_reusejp_949_;
}
else
{
lean_object* v_reuseFailAlloc_951_; 
v_reuseFailAlloc_951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_951_, 0, v_a_945_);
v___x_950_ = v_reuseFailAlloc_951_;
goto v_reusejp_949_;
}
v_reusejp_949_:
{
return v___x_950_;
}
}
}
}
else
{
lean_object* v_a_953_; lean_object* v___x_955_; uint8_t v_isShared_956_; uint8_t v_isSharedCheck_960_; 
lean_dec(v_fst_916_);
lean_dec(v_subst_901_);
lean_dec(v___x_900_);
v_a_953_ = lean_ctor_get(v___x_918_, 0);
v_isSharedCheck_960_ = !lean_is_exclusive(v___x_918_);
if (v_isSharedCheck_960_ == 0)
{
v___x_955_ = v___x_918_;
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
else
{
lean_inc(v_a_953_);
lean_dec(v___x_918_);
v___x_955_ = lean_box(0);
v_isShared_956_ = v_isSharedCheck_960_;
goto v_resetjp_954_;
}
v_resetjp_954_:
{
lean_object* v___x_958_; 
if (v_isShared_956_ == 0)
{
v___x_958_ = v___x_955_;
goto v_reusejp_957_;
}
else
{
lean_object* v_reuseFailAlloc_959_; 
v_reuseFailAlloc_959_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_959_, 0, v_a_953_);
v___x_958_ = v_reuseFailAlloc_959_;
goto v_reusejp_957_;
}
v_reusejp_957_:
{
return v___x_958_;
}
}
}
}
else
{
lean_object* v_a_961_; lean_object* v___x_963_; uint8_t v_isShared_964_; uint8_t v_isSharedCheck_968_; 
lean_dec(v_subst_901_);
lean_dec(v___x_900_);
v_a_961_ = lean_ctor_get(v___x_914_, 0);
v_isSharedCheck_968_ = !lean_is_exclusive(v___x_914_);
if (v_isSharedCheck_968_ == 0)
{
v___x_963_ = v___x_914_;
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
else
{
lean_inc(v_a_961_);
lean_dec(v___x_914_);
v___x_963_ = lean_box(0);
v_isShared_964_ = v_isSharedCheck_968_;
goto v_resetjp_962_;
}
v_resetjp_962_:
{
lean_object* v___x_966_; 
if (v_isShared_964_ == 0)
{
v___x_966_ = v___x_963_;
goto v_reusejp_965_;
}
else
{
lean_object* v_reuseFailAlloc_967_; 
v_reuseFailAlloc_967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_967_, 0, v_a_961_);
v___x_966_ = v_reuseFailAlloc_967_;
goto v_reusejp_965_;
}
v_reusejp_965_:
{
return v___x_966_;
}
}
}
}
else
{
lean_object* v_a_969_; lean_object* v___x_971_; uint8_t v_isShared_972_; uint8_t v_isSharedCheck_976_; 
lean_dec(v_subst_901_);
lean_dec(v___x_900_);
lean_dec(v___x_898_);
v_a_969_ = lean_ctor_get(v___x_910_, 0);
v_isSharedCheck_976_ = !lean_is_exclusive(v___x_910_);
if (v_isSharedCheck_976_ == 0)
{
v___x_971_ = v___x_910_;
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
else
{
lean_inc(v_a_969_);
lean_dec(v___x_910_);
v___x_971_ = lean_box(0);
v_isShared_972_ = v_isSharedCheck_976_;
goto v_resetjp_970_;
}
v_resetjp_970_:
{
lean_object* v___x_974_; 
if (v_isShared_972_ == 0)
{
v___x_974_ = v___x_971_;
goto v_reusejp_973_;
}
else
{
lean_object* v_reuseFailAlloc_975_; 
v_reuseFailAlloc_975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_975_, 0, v_a_969_);
v___x_974_ = v_reuseFailAlloc_975_;
goto v_reusejp_973_;
}
v_reusejp_973_:
{
return v___x_974_;
}
}
}
}
else
{
lean_object* v_a_977_; lean_object* v___x_979_; uint8_t v_isShared_980_; uint8_t v_isSharedCheck_984_; 
lean_dec(v_subst_901_);
lean_dec(v___x_900_);
lean_dec(v_xNamePrefix_899_);
lean_dec(v___x_898_);
lean_dec_ref(v_a_897_);
lean_dec(v_mvarId_896_);
v_a_977_ = lean_ctor_get(v___x_908_, 0);
v_isSharedCheck_984_ = !lean_is_exclusive(v___x_908_);
if (v_isSharedCheck_984_ == 0)
{
v___x_979_ = v___x_908_;
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
else
{
lean_inc(v_a_977_);
lean_dec(v___x_908_);
v___x_979_ = lean_box(0);
v_isShared_980_ = v_isSharedCheck_984_;
goto v_resetjp_978_;
}
v_resetjp_978_:
{
lean_object* v___x_982_; 
if (v_isShared_980_ == 0)
{
v___x_982_ = v___x_979_;
goto v_reusejp_981_;
}
else
{
lean_object* v_reuseFailAlloc_983_; 
v_reuseFailAlloc_983_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_983_, 0, v_a_977_);
v___x_982_ = v_reuseFailAlloc_983_;
goto v_reusejp_981_;
}
v_reusejp_981_:
{
return v___x_982_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_895_ = stack[0].m_obj;
lean_object* v_mvarId_896_ = stack[1].m_obj;
lean_object* v_a_897_ = stack[2].m_obj;
lean_object* v___x_898_ = stack[3].m_obj;
lean_object* v_xNamePrefix_899_ = stack[4].m_obj;
lean_object* v___x_900_ = stack[5].m_obj;
lean_object* v_subst_901_ = stack[6].m_obj;
uint8_t v___x_902_ = stack[7].m_num;
lean_object* v___y_903_ = stack[8].m_obj;
lean_object* v___y_904_ = stack[9].m_obj;
lean_object* v___y_905_ = stack[10].m_obj;
lean_object* v___y_906_ = stack[11].m_obj;
lean_object* v_res_985_;
v_res_985_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(v___x_895_, v_mvarId_896_, v_a_897_, v___x_898_, v_xNamePrefix_899_, v___x_900_, v_subst_901_, v___x_902_, v___y_903_, v___y_904_, v___y_905_, v___y_906_);
stack->m_obj
 = v_res_985_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed(lean_object* v___x_986_, lean_object* v_mvarId_987_, lean_object* v_a_988_, lean_object* v___x_989_, lean_object* v_xNamePrefix_990_, lean_object* v___x_991_, lean_object* v_subst_992_, lean_object* v___x_993_, lean_object* v___y_994_, lean_object* v___y_995_, lean_object* v___y_996_, lean_object* v___y_997_, lean_object* v___y_998_){
_start:
{
uint8_t v___x_3751__boxed_999_; lean_object* v_res_1000_; 
v___x_3751__boxed_999_ = lean_unbox(v___x_993_);
v_res_1000_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(v___x_986_, v_mvarId_987_, v_a_988_, v___x_989_, v_xNamePrefix_990_, v___x_991_, v_subst_992_, v___x_3751__boxed_999_, v___y_994_, v___y_995_, v___y_996_, v___y_997_);
lean_dec(v___y_997_);
lean_dec_ref(v___y_996_);
lean_dec(v___y_995_);
lean_dec_ref(v___y_994_);
return v_res_1000_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(lean_object* v_fst_1001_, size_t v_sz_1002_, size_t v_i_1003_, lean_object* v_bs_1004_){
_start:
{
uint8_t v___x_1005_; 
v___x_1005_ = lean_usize_dec_lt(v_i_1003_, v_sz_1002_);
if (v___x_1005_ == 0)
{
return v_bs_1004_;
}
else
{
lean_object* v_v_1006_; lean_object* v___x_1007_; lean_object* v_bs_x27_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; size_t v___x_1011_; size_t v___x_1012_; lean_object* v___x_1013_; 
v_v_1006_ = lean_array_uget(v_bs_1004_, v_i_1003_);
v___x_1007_ = lean_unsigned_to_nat(0u);
v_bs_x27_1008_ = lean_array_uset(v_bs_1004_, v_i_1003_, v___x_1007_);
v___x_1009_ = l_Lean_Meta_FVarSubst_get(v_fst_1001_, v_v_1006_);
v___x_1010_ = l_Lean_Expr_fvarId_x21(v___x_1009_);
lean_dec_ref(v___x_1009_);
v___x_1011_ = ((size_t)1ULL);
v___x_1012_ = lean_usize_add(v_i_1003_, v___x_1011_);
v___x_1013_ = lean_array_uset(v_bs_x27_1008_, v_i_1003_, v___x_1010_);
v_i_1003_ = v___x_1012_;
v_bs_1004_ = v___x_1013_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_fst_1001_ = stack[0].m_obj;
size_t v_sz_1002_ = stack[1].m_num;
size_t v_i_1003_ = stack[2].m_num;
lean_object* v_bs_1004_ = stack[3].m_obj;
lean_object* v_res_1015_;
v_res_1015_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_1001_, v_sz_1002_, v_i_1003_, v_bs_1004_);
stack->m_obj
 = v_res_1015_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1___boxed(lean_object* v_fst_1016_, lean_object* v_sz_1017_, lean_object* v_i_1018_, lean_object* v_bs_1019_){
_start:
{
size_t v_sz_boxed_1020_; size_t v_i_boxed_1021_; lean_object* v_res_1022_; 
v_sz_boxed_1020_ = lean_unbox_usize(v_sz_1017_);
lean_dec(v_sz_1017_);
v_i_boxed_1021_ = lean_unbox_usize(v_i_1018_);
lean_dec(v_i_1018_);
v_res_1022_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_1016_, v_sz_boxed_1020_, v_i_boxed_1021_, v_bs_1019_);
lean_dec(v_fst_1016_);
return v_res_1022_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(lean_object* v_sizes_1023_, lean_object* v_fst_1024_, lean_object* v_a_1025_, lean_object* v_xNamePrefix_1026_, size_t v_sz_1027_, size_t v_i_1028_, lean_object* v_bs_1029_, lean_object* v___y_1030_, lean_object* v___y_1031_, lean_object* v___y_1032_, lean_object* v___y_1033_){
_start:
{
uint8_t v___x_1035_; 
v___x_1035_ = lean_usize_dec_lt(v_i_1028_, v_sz_1027_);
if (v___x_1035_ == 0)
{
lean_object* v___x_1036_; 
lean_dec(v_xNamePrefix_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_fst_1024_);
v___x_1036_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1036_, 0, v_bs_1029_);
return v___x_1036_;
}
else
{
lean_object* v_v_1037_; lean_object* v_mvarId_1038_; lean_object* v_newHs_1039_; lean_object* v_subst_1040_; lean_object* v___x_1041_; lean_object* v_bs_x27_1042_; lean_object* v_a_1044_; lean_object* v___x_1049_; lean_object* v___x_1050_; uint8_t v___x_1051_; 
v_v_1037_ = lean_array_uget_borrowed(v_bs_1029_, v_i_1028_);
v_mvarId_1038_ = lean_ctor_get(v_v_1037_, 0);
lean_inc(v_mvarId_1038_);
v_newHs_1039_ = lean_ctor_get(v_v_1037_, 1);
lean_inc_ref(v_newHs_1039_);
v_subst_1040_ = lean_ctor_get(v_v_1037_, 2);
lean_inc(v_subst_1040_);
v___x_1041_ = lean_unsigned_to_nat(0u);
v_bs_x27_1042_ = lean_array_uset(v_bs_1029_, v_i_1028_, v___x_1041_);
v___x_1049_ = lean_usize_to_nat(v_i_1028_);
v___x_1050_ = lean_array_get_size(v_sizes_1023_);
v___x_1051_ = lean_nat_dec_lt(v___x_1049_, v___x_1050_);
if (v___x_1051_ == 0)
{
lean_object* v___x_1052_; 
lean_dec(v___x_1049_);
lean_inc(v_fst_1024_);
v___x_1052_ = l_Lean_Meta_substCore(v_mvarId_1038_, v_fst_1024_, v___x_1051_, v_subst_1040_, v___x_1035_, v___x_1051_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1052_) == 0)
{
lean_object* v_a_1053_; lean_object* v_fst_1054_; lean_object* v_snd_1055_; size_t v_sz_1056_; size_t v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; 
v_a_1053_ = lean_ctor_get(v___x_1052_, 0);
lean_inc(v_a_1053_);
lean_dec_ref_known(v___x_1052_, 1);
v_fst_1054_ = lean_ctor_get(v_a_1053_, 0);
lean_inc(v_fst_1054_);
v_snd_1055_ = lean_ctor_get(v_a_1053_, 1);
lean_inc(v_snd_1055_);
lean_dec(v_a_1053_);
v_sz_1056_ = lean_array_size(v_newHs_1039_);
v___x_1057_ = ((size_t)0ULL);
v___x_1058_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_1054_, v_sz_1056_, v___x_1057_, v_newHs_1039_);
v___x_1059_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0));
v___x_1060_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1060_, 0, v_snd_1055_);
lean_ctor_set(v___x_1060_, 1, v___x_1059_);
lean_ctor_set(v___x_1060_, 2, v___x_1058_);
lean_ctor_set(v___x_1060_, 3, v_fst_1054_);
v_a_1044_ = v___x_1060_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1068_; 
lean_dec_ref(v_bs_x27_1042_);
lean_dec_ref(v_newHs_1039_);
lean_dec(v_xNamePrefix_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_fst_1024_);
v_a_1061_ = lean_ctor_get(v___x_1052_, 0);
v_isSharedCheck_1068_ = !lean_is_exclusive(v___x_1052_);
if (v_isSharedCheck_1068_ == 0)
{
v___x_1063_ = v___x_1052_;
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_a_1061_);
lean_dec(v___x_1052_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1068_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1064_ == 0)
{
v___x_1066_ = v___x_1063_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1067_; 
v_reuseFailAlloc_1067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1067_, 0, v_a_1061_);
v___x_1066_ = v_reuseFailAlloc_1067_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
return v___x_1066_;
}
}
}
}
else
{
lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___f_1074_; lean_object* v___x_1075_; 
lean_dec_ref(v_newHs_1039_);
lean_inc(v_fst_1024_);
v___x_1069_ = l_Lean_Meta_FVarSubst_get(v_subst_1040_, v_fst_1024_);
v___x_1070_ = l_Lean_Expr_fvarId_x21(v___x_1069_);
lean_dec_ref(v___x_1069_);
v___x_1071_ = lean_array_fget_borrowed(v_sizes_1023_, v___x_1049_);
lean_dec(v___x_1049_);
lean_inc(v___x_1070_);
v___x_1072_ = l_Lean_mkFVar(v___x_1070_);
v___x_1073_ = lean_box(v___x_1035_);
lean_inc(v_xNamePrefix_1026_);
lean_inc(v___x_1071_);
lean_inc_ref(v_a_1025_);
lean_inc(v_mvarId_1038_);
v___f_1074_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1074_, 0, v___x_1072_);
lean_closure_set(v___f_1074_, 1, v_mvarId_1038_);
lean_closure_set(v___f_1074_, 2, v_a_1025_);
lean_closure_set(v___f_1074_, 3, v___x_1071_);
lean_closure_set(v___f_1074_, 4, v_xNamePrefix_1026_);
lean_closure_set(v___f_1074_, 5, v___x_1070_);
lean_closure_set(v___f_1074_, 6, v_subst_1040_);
lean_closure_set(v___f_1074_, 7, v___x_1073_);
v___x_1075_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_1038_, v___f_1074_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v_a_1076_; 
v_a_1076_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_a_1076_);
lean_dec_ref_known(v___x_1075_, 1);
v_a_1044_ = v_a_1076_;
goto v___jp_1043_;
}
else
{
lean_object* v_a_1077_; lean_object* v___x_1079_; uint8_t v_isShared_1080_; uint8_t v_isSharedCheck_1084_; 
lean_dec_ref(v_bs_x27_1042_);
lean_dec(v_xNamePrefix_1026_);
lean_dec_ref(v_a_1025_);
lean_dec(v_fst_1024_);
v_a_1077_ = lean_ctor_get(v___x_1075_, 0);
v_isSharedCheck_1084_ = !lean_is_exclusive(v___x_1075_);
if (v_isSharedCheck_1084_ == 0)
{
v___x_1079_ = v___x_1075_;
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
else
{
lean_inc(v_a_1077_);
lean_dec(v___x_1075_);
v___x_1079_ = lean_box(0);
v_isShared_1080_ = v_isSharedCheck_1084_;
goto v_resetjp_1078_;
}
v_resetjp_1078_:
{
lean_object* v___x_1082_; 
if (v_isShared_1080_ == 0)
{
v___x_1082_ = v___x_1079_;
goto v_reusejp_1081_;
}
else
{
lean_object* v_reuseFailAlloc_1083_; 
v_reuseFailAlloc_1083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1083_, 0, v_a_1077_);
v___x_1082_ = v_reuseFailAlloc_1083_;
goto v_reusejp_1081_;
}
v_reusejp_1081_:
{
return v___x_1082_;
}
}
}
}
v___jp_1043_:
{
size_t v___x_1045_; size_t v___x_1046_; lean_object* v___x_1047_; 
v___x_1045_ = ((size_t)1ULL);
v___x_1046_ = lean_usize_add(v_i_1028_, v___x_1045_);
v___x_1047_ = lean_array_uset(v_bs_x27_1042_, v_i_1028_, v_a_1044_);
v_i_1028_ = v___x_1046_;
v_bs_1029_ = v___x_1047_;
goto _start;
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_sizes_1023_ = stack[0].m_obj;
lean_object* v_fst_1024_ = stack[1].m_obj;
lean_object* v_a_1025_ = stack[2].m_obj;
lean_object* v_xNamePrefix_1026_ = stack[3].m_obj;
size_t v_sz_1027_ = stack[4].m_num;
size_t v_i_1028_ = stack[5].m_num;
lean_object* v_bs_1029_ = stack[6].m_obj;
lean_object* v___y_1030_ = stack[7].m_obj;
lean_object* v___y_1031_ = stack[8].m_obj;
lean_object* v___y_1032_ = stack[9].m_obj;
lean_object* v___y_1033_ = stack[10].m_obj;
lean_object* v_res_1085_;
v_res_1085_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1023_, v_fst_1024_, v_a_1025_, v_xNamePrefix_1026_, v_sz_1027_, v_i_1028_, v_bs_1029_, v___y_1030_, v___y_1031_, v___y_1032_, v___y_1033_);
stack->m_obj
 = v_res_1085_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___boxed(lean_object* v_sizes_1086_, lean_object* v_fst_1087_, lean_object* v_a_1088_, lean_object* v_xNamePrefix_1089_, lean_object* v_sz_1090_, lean_object* v_i_1091_, lean_object* v_bs_1092_, lean_object* v___y_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
size_t v_sz_boxed_1098_; size_t v_i_boxed_1099_; lean_object* v_res_1100_; 
v_sz_boxed_1098_ = lean_unbox_usize(v_sz_1090_);
lean_dec(v_sz_1090_);
v_i_boxed_1099_ = lean_unbox_usize(v_i_1091_);
lean_dec(v_i_1091_);
v_res_1100_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1086_, v_fst_1087_, v_a_1088_, v_xNamePrefix_1089_, v_sz_boxed_1098_, v_i_boxed_1099_, v_bs_1092_, v___y_1093_, v___y_1094_, v___y_1095_, v___y_1096_);
lean_dec(v___y_1096_);
lean_dec_ref(v___y_1095_);
lean_dec(v___y_1094_);
lean_dec_ref(v___y_1093_);
lean_dec_ref(v_sizes_1086_);
return v_res_1100_;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; 
v___x_1107_ = lean_box(0);
v___x_1108_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__3));
v___x_1109_ = l_Lean_mkConst(v___x_1108_, v___x_1107_);
return v___x_1109_;
}
}
lean_object* l_Lean_Meta_caseArraySizes___lam__0(lean_object* v___x_1113_, lean_object* v___x_1114_, lean_object* v_mvarId_1115_, lean_object* v_sizes_1116_, lean_object* v_hNamePrefix_1117_, lean_object* v_a_1118_, lean_object* v_xNamePrefix_1119_, lean_object* v___y_1120_, lean_object* v___y_1121_, lean_object* v___y_1122_, lean_object* v___y_1123_){
_start:
{
lean_object* v___x_1125_; 
v___x_1125_ = l_Lean_Meta_mkAppM(v___x_1113_, v___x_1114_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1125_) == 0)
{
lean_object* v_a_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_a_1126_ = lean_ctor_get(v___x_1125_, 0);
lean_inc(v_a_1126_);
lean_dec_ref_known(v___x_1125_, 1);
v___x_1127_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__1));
v___x_1128_ = lean_obj_once(&l_Lean_Meta_caseArraySizes___lam__0___closed__4, &l_Lean_Meta_caseArraySizes___lam__0___closed__4_once, _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4);
v___x_1129_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__6));
v___x_1130_ = l_Lean_MVarId_assertExt(v_mvarId_1115_, v___x_1127_, v___x_1128_, v_a_1126_, v___x_1129_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_object* v_a_1131_; uint8_t v___x_1132_; lean_object* v___x_1133_; 
v_a_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_a_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = 0;
v___x_1133_ = l_Lean_Meta_intro1Core(v_a_1131_, v___x_1132_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1133_) == 0)
{
lean_object* v_a_1134_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1137_; 
v_a_1134_ = lean_ctor_get(v___x_1133_, 0);
lean_inc(v_a_1134_);
lean_dec_ref_known(v___x_1133_, 1);
v_fst_1135_ = lean_ctor_get(v_a_1134_, 0);
lean_inc(v_fst_1135_);
v_snd_1136_ = lean_ctor_get(v_a_1134_, 1);
lean_inc(v_snd_1136_);
lean_dec(v_a_1134_);
v___x_1137_ = l_Lean_Meta_intro1Core(v_snd_1136_, v___x_1132_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1137_) == 0)
{
lean_object* v_a_1138_; lean_object* v_fst_1139_; lean_object* v_snd_1140_; size_t v_sz_1141_; size_t v___x_1142_; lean_object* v___x_1143_; uint8_t v___x_1144_; lean_object* v___x_1145_; 
v_a_1138_ = lean_ctor_get(v___x_1137_, 0);
lean_inc(v_a_1138_);
lean_dec_ref_known(v___x_1137_, 1);
v_fst_1139_ = lean_ctor_get(v_a_1138_, 0);
lean_inc(v_fst_1139_);
v_snd_1140_ = lean_ctor_get(v_a_1138_, 1);
lean_inc(v_snd_1140_);
lean_dec(v_a_1138_);
v_sz_1141_ = lean_array_size(v_sizes_1116_);
v___x_1142_ = ((size_t)0ULL);
lean_inc_ref(v_sizes_1116_);
v___x_1143_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_1141_, v___x_1142_, v_sizes_1116_);
v___x_1144_ = 1;
v___x_1145_ = l_Lean_Meta_caseValues(v_snd_1140_, v_fst_1135_, v___x_1143_, v_hNamePrefix_1117_, v___x_1144_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
if (lean_obj_tag(v___x_1145_) == 0)
{
lean_object* v_a_1146_; size_t v_sz_1147_; lean_object* v___x_1148_; 
v_a_1146_ = lean_ctor_get(v___x_1145_, 0);
lean_inc(v_a_1146_);
lean_dec_ref_known(v___x_1145_, 1);
v_sz_1147_ = lean_array_size(v_a_1146_);
v___x_1148_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1116_, v_fst_1139_, v_a_1118_, v_xNamePrefix_1119_, v_sz_1147_, v___x_1142_, v_a_1146_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
lean_dec_ref(v_sizes_1116_);
return v___x_1148_;
}
else
{
lean_object* v_a_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1156_; 
lean_dec(v_fst_1139_);
lean_dec(v_xNamePrefix_1119_);
lean_dec_ref(v_a_1118_);
lean_dec_ref(v_sizes_1116_);
v_a_1149_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1156_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1151_ = v___x_1145_;
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_a_1149_);
lean_dec(v___x_1145_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1156_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
lean_object* v___x_1154_; 
if (v_isShared_1152_ == 0)
{
v___x_1154_ = v___x_1151_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_a_1149_);
v___x_1154_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
return v___x_1154_;
}
}
}
}
else
{
lean_object* v_a_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1164_; 
lean_dec(v_fst_1135_);
lean_dec(v_xNamePrefix_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_hNamePrefix_1117_);
lean_dec_ref(v_sizes_1116_);
v_a_1157_ = lean_ctor_get(v___x_1137_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v___x_1137_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1159_ = v___x_1137_;
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_a_1157_);
lean_dec(v___x_1137_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1164_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
lean_object* v___x_1162_; 
if (v_isShared_1160_ == 0)
{
v___x_1162_ = v___x_1159_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_a_1157_);
v___x_1162_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
return v___x_1162_;
}
}
}
}
else
{
lean_object* v_a_1165_; lean_object* v___x_1167_; uint8_t v_isShared_1168_; uint8_t v_isSharedCheck_1172_; 
lean_dec(v_xNamePrefix_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_hNamePrefix_1117_);
lean_dec_ref(v_sizes_1116_);
v_a_1165_ = lean_ctor_get(v___x_1133_, 0);
v_isSharedCheck_1172_ = !lean_is_exclusive(v___x_1133_);
if (v_isSharedCheck_1172_ == 0)
{
v___x_1167_ = v___x_1133_;
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
else
{
lean_inc(v_a_1165_);
lean_dec(v___x_1133_);
v___x_1167_ = lean_box(0);
v_isShared_1168_ = v_isSharedCheck_1172_;
goto v_resetjp_1166_;
}
v_resetjp_1166_:
{
lean_object* v___x_1170_; 
if (v_isShared_1168_ == 0)
{
v___x_1170_ = v___x_1167_;
goto v_reusejp_1169_;
}
else
{
lean_object* v_reuseFailAlloc_1171_; 
v_reuseFailAlloc_1171_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1171_, 0, v_a_1165_);
v___x_1170_ = v_reuseFailAlloc_1171_;
goto v_reusejp_1169_;
}
v_reusejp_1169_:
{
return v___x_1170_;
}
}
}
}
else
{
lean_object* v_a_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1180_; 
lean_dec(v_xNamePrefix_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_hNamePrefix_1117_);
lean_dec_ref(v_sizes_1116_);
v_a_1173_ = lean_ctor_get(v___x_1130_, 0);
v_isSharedCheck_1180_ = !lean_is_exclusive(v___x_1130_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1175_ = v___x_1130_;
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_a_1173_);
lean_dec(v___x_1130_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1180_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1176_ == 0)
{
v___x_1178_ = v___x_1175_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v_a_1173_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
else
{
lean_object* v_a_1181_; lean_object* v___x_1183_; uint8_t v_isShared_1184_; uint8_t v_isSharedCheck_1188_; 
lean_dec(v_xNamePrefix_1119_);
lean_dec_ref(v_a_1118_);
lean_dec(v_hNamePrefix_1117_);
lean_dec_ref(v_sizes_1116_);
lean_dec(v_mvarId_1115_);
v_a_1181_ = lean_ctor_get(v___x_1125_, 0);
v_isSharedCheck_1188_ = !lean_is_exclusive(v___x_1125_);
if (v_isSharedCheck_1188_ == 0)
{
v___x_1183_ = v___x_1125_;
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
else
{
lean_inc(v_a_1181_);
lean_dec(v___x_1125_);
v___x_1183_ = lean_box(0);
v_isShared_1184_ = v_isSharedCheck_1188_;
goto v_resetjp_1182_;
}
v_resetjp_1182_:
{
lean_object* v___x_1186_; 
if (v_isShared_1184_ == 0)
{
v___x_1186_ = v___x_1183_;
goto v_reusejp_1185_;
}
else
{
lean_object* v_reuseFailAlloc_1187_; 
v_reuseFailAlloc_1187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1187_, 0, v_a_1181_);
v___x_1186_ = v_reuseFailAlloc_1187_;
goto v_reusejp_1185_;
}
v_reusejp_1185_:
{
return v___x_1186_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Meta_caseArraySizes___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_1113_ = stack[0].m_obj;
lean_object* v___x_1114_ = stack[1].m_obj;
lean_object* v_mvarId_1115_ = stack[2].m_obj;
lean_object* v_sizes_1116_ = stack[3].m_obj;
lean_object* v_hNamePrefix_1117_ = stack[4].m_obj;
lean_object* v_a_1118_ = stack[5].m_obj;
lean_object* v_xNamePrefix_1119_ = stack[6].m_obj;
lean_object* v___y_1120_ = stack[7].m_obj;
lean_object* v___y_1121_ = stack[8].m_obj;
lean_object* v___y_1122_ = stack[9].m_obj;
lean_object* v___y_1123_ = stack[10].m_obj;
lean_object* v_res_1189_;
v_res_1189_ = l_Lean_Meta_caseArraySizes___lam__0(v___x_1113_, v___x_1114_, v_mvarId_1115_, v_sizes_1116_, v_hNamePrefix_1117_, v_a_1118_, v_xNamePrefix_1119_, v___y_1120_, v___y_1121_, v___y_1122_, v___y_1123_);
stack->m_obj
 = v_res_1189_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0___boxed(lean_object* v___x_1190_, lean_object* v___x_1191_, lean_object* v_mvarId_1192_, lean_object* v_sizes_1193_, lean_object* v_hNamePrefix_1194_, lean_object* v_a_1195_, lean_object* v_xNamePrefix_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_, lean_object* v___y_1199_, lean_object* v___y_1200_, lean_object* v___y_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Lean_Meta_caseArraySizes___lam__0(v___x_1190_, v___x_1191_, v_mvarId_1192_, v_sizes_1193_, v_hNamePrefix_1194_, v_a_1195_, v_xNamePrefix_1196_, v___y_1197_, v___y_1198_, v___y_1199_, v___y_1200_);
lean_dec(v___y_1200_);
lean_dec_ref(v___y_1199_);
lean_dec(v___y_1198_);
lean_dec_ref(v___y_1197_);
return v_res_1202_;
}
}
lean_object* l_Lean_Meta_caseArraySizes(lean_object* v_mvarId_1207_, lean_object* v_fvarId_1208_, lean_object* v_sizes_1209_, lean_object* v_xNamePrefix_1210_, lean_object* v_hNamePrefix_1211_, lean_object* v_a_1212_, lean_object* v_a_1213_, lean_object* v_a_1214_, lean_object* v_a_1215_){
_start:
{
lean_object* v_a_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___f_1222_; lean_object* v___x_1223_; 
v_a_1217_ = l_Lean_mkFVar(v_fvarId_1208_);
v___x_1218_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___closed__1));
v___x_1219_ = lean_unsigned_to_nat(1u);
v___x_1220_ = lean_mk_empty_array_with_capacity(v___x_1219_);
lean_inc_ref(v_a_1217_);
v___x_1221_ = lean_array_push(v___x_1220_, v_a_1217_);
lean_inc(v_mvarId_1207_);
v___f_1222_ = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1222_, 0, v___x_1218_);
lean_closure_set(v___f_1222_, 1, v___x_1221_);
lean_closure_set(v___f_1222_, 2, v_mvarId_1207_);
lean_closure_set(v___f_1222_, 3, v_sizes_1209_);
lean_closure_set(v___f_1222_, 4, v_hNamePrefix_1211_);
lean_closure_set(v___f_1222_, 5, v_a_1217_);
lean_closure_set(v___f_1222_, 6, v_xNamePrefix_1210_);
v___x_1223_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_1207_, v___f_1222_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
return v___x_1223_;
}
}
LEAN_EXPORT void l_Lean_Meta_caseArraySizes_0interp(lean_interpreter_value* stack)
{
lean_object* v_mvarId_1207_ = stack[0].m_obj;
lean_object* v_fvarId_1208_ = stack[1].m_obj;
lean_object* v_sizes_1209_ = stack[2].m_obj;
lean_object* v_xNamePrefix_1210_ = stack[3].m_obj;
lean_object* v_hNamePrefix_1211_ = stack[4].m_obj;
lean_object* v_a_1212_ = stack[5].m_obj;
lean_object* v_a_1213_ = stack[6].m_obj;
lean_object* v_a_1214_ = stack[7].m_obj;
lean_object* v_a_1215_ = stack[8].m_obj;
lean_object* v_res_1224_;
v_res_1224_ = l_Lean_Meta_caseArraySizes(v_mvarId_1207_, v_fvarId_1208_, v_sizes_1209_, v_xNamePrefix_1210_, v_hNamePrefix_1211_, v_a_1212_, v_a_1213_, v_a_1214_, v_a_1215_);
stack->m_obj
 = v_res_1224_;
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___boxed(lean_object* v_mvarId_1225_, lean_object* v_fvarId_1226_, lean_object* v_sizes_1227_, lean_object* v_xNamePrefix_1228_, lean_object* v_hNamePrefix_1229_, lean_object* v_a_1230_, lean_object* v_a_1231_, lean_object* v_a_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Lean_Meta_caseArraySizes(v_mvarId_1225_, v_fvarId_1226_, v_sizes_1227_, v_xNamePrefix_1228_, v_hNamePrefix_1229_, v_a_1230_, v_a_1231_, v_a_1232_, v_a_1233_);
lean_dec(v_a_1233_);
lean_dec_ref(v_a_1232_);
lean_dec(v_a_1231_);
lean_dec_ref(v_a_1230_);
return v_res_1235_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3(lean_object* v_sizes_1236_, lean_object* v_fst_1237_, lean_object* v_a_1238_, lean_object* v_xNamePrefix_1239_, lean_object* v_as_1240_, size_t v_sz_1241_, size_t v_i_1242_, lean_object* v_bs_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1236_, v_fst_1237_, v_a_1238_, v_xNamePrefix_1239_, v_sz_1241_, v_i_1242_, v_bs_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
return v___x_1249_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_sizes_1236_ = stack[0].m_obj;
lean_object* v_fst_1237_ = stack[1].m_obj;
lean_object* v_a_1238_ = stack[2].m_obj;
lean_object* v_xNamePrefix_1239_ = stack[3].m_obj;
lean_object* v_as_1240_ = stack[4].m_obj;
size_t v_sz_1241_ = stack[5].m_num;
size_t v_i_1242_ = stack[6].m_num;
lean_object* v_bs_1243_ = stack[7].m_obj;
lean_object* v___y_1244_ = stack[8].m_obj;
lean_object* v___y_1245_ = stack[9].m_obj;
lean_object* v___y_1246_ = stack[10].m_obj;
lean_object* v___y_1247_ = stack[11].m_obj;
lean_object* v_res_1250_;
v_res_1250_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3(v_sizes_1236_, v_fst_1237_, v_a_1238_, v_xNamePrefix_1239_, v_as_1240_, v_sz_1241_, v_i_1242_, v_bs_1243_, v___y_1244_, v___y_1245_, v___y_1246_, v___y_1247_);
stack->m_obj
 = v_res_1250_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___boxed(lean_object* v_sizes_1251_, lean_object* v_fst_1252_, lean_object* v_a_1253_, lean_object* v_xNamePrefix_1254_, lean_object* v_as_1255_, lean_object* v_sz_1256_, lean_object* v_i_1257_, lean_object* v_bs_1258_, lean_object* v___y_1259_, lean_object* v___y_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_){
_start:
{
size_t v_sz_boxed_1264_; size_t v_i_boxed_1265_; lean_object* v_res_1266_; 
v_sz_boxed_1264_ = lean_unbox_usize(v_sz_1256_);
lean_dec(v_sz_1256_);
v_i_boxed_1265_ = lean_unbox_usize(v_i_1257_);
lean_dec(v_i_1257_);
v_res_1266_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3(v_sizes_1251_, v_fst_1252_, v_a_1253_, v_xNamePrefix_1254_, v_as_1255_, v_sz_boxed_1264_, v_i_boxed_1265_, v_bs_1258_, v___y_1259_, v___y_1260_, v___y_1261_, v___y_1262_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
lean_dec(v___y_1260_);
lean_dec_ref(v___y_1259_);
lean_dec_ref(v_as_1255_);
lean_dec_ref(v_sizes_1251_);
return v_res_1266_;
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
