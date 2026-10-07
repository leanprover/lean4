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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(lean_object* v_msgData_9_, lean_object* v___y_10_, lean_object* v___y_11_, lean_object* v___y_12_, lean_object* v___y_13_){
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
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0___boxed(lean_object* v_msgData_27_, lean_object* v___y_28_, lean_object* v___y_29_, lean_object* v___y_30_, lean_object* v___y_31_, lean_object* v___y_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msgData_27_, v___y_28_, v___y_29_, v___y_30_, v___y_31_);
lean_dec(v___y_31_);
lean_dec_ref(v___y_30_);
lean_dec(v___y_29_);
lean_dec_ref(v___y_28_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(lean_object* v_msg_34_, lean_object* v___y_35_, lean_object* v___y_36_, lean_object* v___y_37_, lean_object* v___y_38_){
_start:
{
lean_object* v_ref_40_; lean_object* v___x_41_; lean_object* v_a_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_50_; 
v_ref_40_ = lean_ctor_get(v___y_37_, 2);
v___x_41_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0_spec__0(v_msg_34_, v___y_35_, v___y_36_, v___y_37_, v___y_38_);
v_a_42_ = lean_ctor_get(v___x_41_, 0);
v_isSharedCheck_50_ = !lean_is_exclusive(v___x_41_);
if (v_isSharedCheck_50_ == 0)
{
v___x_44_ = v___x_41_;
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_a_42_);
lean_dec(v___x_41_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_50_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; lean_object* v___x_48_; 
lean_inc(v_ref_40_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v_ref_40_);
lean_ctor_set(v___x_46_, 1, v_a_42_);
if (v_isShared_45_ == 0)
{
lean_ctor_set_tag(v___x_44_, 1);
lean_ctor_set(v___x_44_, 0, v___x_46_);
v___x_48_ = v___x_44_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v___x_46_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg___boxed(lean_object* v_msg_51_, lean_object* v___y_52_, lean_object* v___y_53_, lean_object* v___y_54_, lean_object* v___y_55_, lean_object* v___y_56_){
_start:
{
lean_object* v_res_57_; 
v_res_57_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_51_, v___y_52_, v___y_53_, v___y_54_, v___y_55_);
lean_dec(v___y_55_);
lean_dec_ref(v___y_54_);
lean_dec(v___y_53_);
lean_dec_ref(v___y_52_);
return v_res_57_;
}
}
static lean_object* _init_l_Lean_Meta_getArrayArgType___closed__3(void){
_start:
{
lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_62_ = ((lean_object*)(l_Lean_Meta_getArrayArgType___closed__2));
v___x_63_ = l_Lean_stringToMessageData(v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType(lean_object* v_a_64_, lean_object* v_a_65_, lean_object* v_a_66_, lean_object* v_a_67_, lean_object* v_a_68_){
_start:
{
lean_object* v___x_70_; 
lean_inc(v_a_68_);
lean_inc_ref(v_a_67_);
lean_inc(v_a_66_);
lean_inc_ref(v_a_65_);
lean_inc_ref(v_a_64_);
v___x_70_ = lean_infer_type(v_a_64_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_70_) == 0)
{
lean_object* v_a_71_; lean_object* v___x_72_; 
v_a_71_ = lean_ctor_get(v___x_70_, 0);
lean_inc(v_a_71_);
lean_dec_ref_known(v___x_70_, 1);
v___x_72_ = l_Lean_Meta_whnfD(v_a_71_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
if (lean_obj_tag(v___x_72_) == 0)
{
lean_object* v_a_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_97_; 
v_a_73_ = lean_ctor_get(v___x_72_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v___x_72_);
if (v_isSharedCheck_97_ == 0)
{
v___x_75_ = v___x_72_;
v_isShared_76_ = v_isSharedCheck_97_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_a_73_);
lean_dec(v___x_72_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_97_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_82_; lean_object* v___x_83_; uint8_t v___x_84_; 
v___x_82_ = ((lean_object*)(l_Lean_Meta_getArrayArgType___closed__1));
v___x_83_ = lean_unsigned_to_nat(1u);
v___x_84_ = l_Lean_Expr_isAppOfArity(v_a_73_, v___x_82_, v___x_83_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v_a_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_96_; 
lean_del_object(v___x_75_);
lean_dec(v_a_73_);
v___x_85_ = lean_obj_once(&l_Lean_Meta_getArrayArgType___closed__3, &l_Lean_Meta_getArrayArgType___closed__3_once, _init_l_Lean_Meta_getArrayArgType___closed__3);
v___x_86_ = l_Lean_indentExpr(v_a_64_);
v___x_87_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_85_);
lean_ctor_set(v___x_87_, 1, v___x_86_);
v___x_88_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v___x_87_, v_a_65_, v_a_66_, v_a_67_, v_a_68_);
v_a_89_ = lean_ctor_get(v___x_88_, 0);
v_isSharedCheck_96_ = !lean_is_exclusive(v___x_88_);
if (v_isSharedCheck_96_ == 0)
{
v___x_91_ = v___x_88_;
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_a_89_);
lean_dec(v___x_88_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_96_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
lean_object* v___x_94_; 
if (v_isShared_92_ == 0)
{
v___x_94_ = v___x_91_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_a_89_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
else
{
lean_dec_ref(v_a_64_);
goto v___jp_77_;
}
v___jp_77_:
{
lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_78_ = l_Lean_Expr_appArg_x21(v_a_73_);
lean_dec(v_a_73_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 0, v___x_78_);
v___x_80_ = v___x_75_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
else
{
lean_dec_ref(v_a_64_);
return v___x_72_;
}
}
else
{
lean_dec_ref(v_a_64_);
return v___x_70_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getArrayArgType___boxed(lean_object* v_a_98_, lean_object* v_a_99_, lean_object* v_a_100_, lean_object* v_a_101_, lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
lean_object* v_res_104_; 
v_res_104_ = l_Lean_Meta_getArrayArgType(v_a_98_, v_a_99_, v_a_100_, v_a_101_, v_a_102_);
lean_dec(v_a_102_);
lean_dec_ref(v_a_101_);
lean_dec(v_a_100_);
lean_dec_ref(v_a_99_);
return v_res_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(lean_object* v_00_u03b1_105_, lean_object* v_msg_106_, lean_object* v___y_107_, lean_object* v___y_108_, lean_object* v___y_109_, lean_object* v___y_110_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___redArg(v_msg_106_, v___y_107_, v___y_108_, v___y_109_, v___y_110_);
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0___boxed(lean_object* v_00_u03b1_113_, lean_object* v_msg_114_, lean_object* v___y_115_, lean_object* v___y_116_, lean_object* v___y_117_, lean_object* v___y_118_, lean_object* v___y_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_throwError___at___00Lean_Meta_getArrayArgType_spec__0(v_00_u03b1_113_, v_msg_114_, v___y_115_, v___y_116_, v___y_117_, v___y_118_);
lean_dec(v___y_118_);
lean_dec_ref(v___y_117_);
lean_dec(v___y_116_);
lean_dec_ref(v___y_115_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(lean_object* v_a_125_, lean_object* v_i_126_, lean_object* v_n_127_, lean_object* v_h_128_, lean_object* v_a_129_, lean_object* v_a_130_, lean_object* v_a_131_, lean_object* v_a_132_){
_start:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v___x_134_ = l_Lean_mkRawNatLit(v_i_126_);
v___x_135_ = l_Lean_mkRawNatLit(v_n_127_);
lean_inc_ref(v___x_134_);
v___x_136_ = l_Lean_Meta_mkLt(v___x_134_, v___x_135_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_136_) == 0)
{
lean_object* v_a_137_; lean_object* v___x_138_; 
v_a_137_ = lean_ctor_get(v___x_136_, 0);
lean_inc(v_a_137_);
lean_dec_ref_known(v___x_136_, 1);
v___x_138_ = l_Lean_Meta_mkDecideProof(v_a_137_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
if (lean_obj_tag(v___x_138_) == 0)
{
lean_object* v_a_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; 
v_a_139_ = lean_ctor_get(v___x_138_, 0);
lean_inc(v_a_139_);
lean_dec_ref_known(v___x_138_, 1);
v___x_140_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___closed__1));
v___x_141_ = lean_unsigned_to_nat(4u);
v___x_142_ = lean_mk_empty_array_with_capacity(v___x_141_);
v___x_143_ = lean_array_push(v___x_142_, v_a_125_);
v___x_144_ = lean_array_push(v___x_143_, v___x_134_);
v___x_145_ = lean_array_push(v___x_144_, v_h_128_);
v___x_146_ = lean_array_push(v___x_145_, v_a_139_);
v___x_147_ = l_Lean_Meta_mkAppM(v___x_140_, v___x_146_, v_a_129_, v_a_130_, v_a_131_, v_a_132_);
return v___x_147_;
}
else
{
lean_dec_ref(v___x_134_);
lean_dec_ref(v_h_128_);
lean_dec_ref(v_a_125_);
return v___x_138_;
}
}
else
{
lean_dec_ref(v___x_134_);
lean_dec_ref(v_h_128_);
lean_dec_ref(v_a_125_);
return v___x_136_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit___boxed(lean_object* v_a_148_, lean_object* v_i_149_, lean_object* v_n_150_, lean_object* v_h_151_, lean_object* v_a_152_, lean_object* v_a_153_, lean_object* v_a_154_, lean_object* v_a_155_, lean_object* v_a_156_){
_start:
{
lean_object* v_res_157_; 
v_res_157_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_148_, v_i_149_, v_n_150_, v_h_151_, v_a_152_, v_a_153_, v_a_154_, v_a_155_);
lean_dec(v_a_155_);
lean_dec_ref(v_a_154_);
lean_dec(v_a_153_);
lean_dec_ref(v_a_152_);
return v_res_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(lean_object* v_mvarId_158_, lean_object* v_xs_159_, uint8_t v___x_160_, lean_object* v_args_161_, lean_object* v_a_162_, lean_object* v_heq_163_, lean_object* v___y_164_, lean_object* v___y_165_, lean_object* v___y_166_, lean_object* v___y_167_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_Lean_MVarId_getType(v_mvarId_158_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_a_170_; lean_object* v___x_171_; uint8_t v___x_172_; uint8_t v___x_173_; lean_object* v___x_174_; 
v_a_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_a_170_);
lean_dec_ref_known(v___x_169_, 1);
v___x_171_ = lean_array_push(v_xs_159_, v_heq_163_);
v___x_172_ = 1;
v___x_173_ = 1;
v___x_174_ = l_Lean_Meta_mkForallFVars(v___x_171_, v_a_170_, v___x_160_, v___x_172_, v___x_172_, v___x_173_, v___y_164_, v___y_165_, v___y_166_, v___y_167_);
lean_dec_ref(v___x_171_);
if (lean_obj_tag(v___x_174_) == 0)
{
lean_object* v_a_175_; lean_object* v___x_177_; uint8_t v_isShared_178_; uint8_t v_isSharedCheck_184_; 
v_a_175_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_184_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_184_ == 0)
{
v___x_177_ = v___x_174_;
v_isShared_178_ = v_isSharedCheck_184_;
goto v_resetjp_176_;
}
else
{
lean_inc(v_a_175_);
lean_dec(v___x_174_);
v___x_177_ = lean_box(0);
v_isShared_178_ = v_isSharedCheck_184_;
goto v_resetjp_176_;
}
v_resetjp_176_:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_182_; 
v___x_179_ = lean_array_push(v_args_161_, v_a_162_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v_a_175_);
lean_ctor_set(v___x_180_, 1, v___x_179_);
if (v_isShared_178_ == 0)
{
lean_ctor_set(v___x_177_, 0, v___x_180_);
v___x_182_ = v___x_177_;
goto v_reusejp_181_;
}
else
{
lean_object* v_reuseFailAlloc_183_; 
v_reuseFailAlloc_183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_183_, 0, v___x_180_);
v___x_182_ = v_reuseFailAlloc_183_;
goto v_reusejp_181_;
}
v_reusejp_181_:
{
return v___x_182_;
}
}
}
else
{
lean_object* v_a_185_; lean_object* v___x_187_; uint8_t v_isShared_188_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_a_162_);
lean_dec_ref(v_args_161_);
v_a_185_ = lean_ctor_get(v___x_174_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_174_);
if (v_isSharedCheck_192_ == 0)
{
v___x_187_ = v___x_174_;
v_isShared_188_ = v_isSharedCheck_192_;
goto v_resetjp_186_;
}
else
{
lean_inc(v_a_185_);
lean_dec(v___x_174_);
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
lean_dec_ref(v_heq_163_);
lean_dec_ref(v_a_162_);
lean_dec_ref(v_args_161_);
lean_dec_ref(v_xs_159_);
v_a_193_ = lean_ctor_get(v___x_169_, 0);
v_isSharedCheck_200_ = !lean_is_exclusive(v___x_169_);
if (v_isSharedCheck_200_ == 0)
{
v___x_195_ = v___x_169_;
v_isShared_196_ = v_isSharedCheck_200_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_a_193_);
lean_dec(v___x_169_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed(lean_object* v_mvarId_201_, lean_object* v_xs_202_, lean_object* v___x_203_, lean_object* v_args_204_, lean_object* v_a_205_, lean_object* v_heq_206_, lean_object* v___y_207_, lean_object* v___y_208_, lean_object* v___y_209_, lean_object* v___y_210_, lean_object* v___y_211_){
_start:
{
uint8_t v___x_1166__boxed_212_; lean_object* v_res_213_; 
v___x_1166__boxed_212_ = lean_unbox(v___x_203_);
v_res_213_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0(v_mvarId_201_, v_xs_202_, v___x_1166__boxed_212_, v_args_204_, v_a_205_, v_heq_206_, v___y_207_, v___y_208_, v___y_209_, v___y_210_);
lean_dec(v___y_210_);
lean_dec_ref(v___y_209_);
lean_dec(v___y_208_);
lean_dec_ref(v___y_207_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(lean_object* v_k_214_, lean_object* v_b_215_, lean_object* v___y_216_, lean_object* v___y_217_, lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v___x_221_; 
lean_inc(v___y_219_);
lean_inc_ref(v___y_218_);
lean_inc(v___y_217_);
lean_inc_ref(v___y_216_);
v___x_221_ = lean_apply_6(v_k_214_, v_b_215_, v___y_216_, v___y_217_, v___y_218_, v___y_219_, lean_box(0));
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed(lean_object* v_k_222_, lean_object* v_b_223_, lean_object* v___y_224_, lean_object* v___y_225_, lean_object* v___y_226_, lean_object* v___y_227_, lean_object* v___y_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0(v_k_222_, v_b_223_, v___y_224_, v___y_225_, v___y_226_, v___y_227_);
lean_dec(v___y_227_);
lean_dec_ref(v___y_226_);
lean_dec(v___y_225_);
lean_dec_ref(v___y_224_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(lean_object* v_name_230_, uint8_t v_bi_231_, lean_object* v_type_232_, lean_object* v_k_233_, uint8_t v_kind_234_, lean_object* v___y_235_, lean_object* v___y_236_, lean_object* v___y_237_, lean_object* v___y_238_){
_start:
{
lean_object* v___f_240_; lean_object* v___x_241_; 
v___f_240_ = lean_alloc_closure((void*)(l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___lam__0___boxed), 7, 1);
lean_closure_set(v___f_240_, 0, v_k_233_);
v___x_241_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withLocalDeclImp(lean_box(0), v_name_230_, v_bi_231_, v_type_232_, v___f_240_, v_kind_234_, v___y_235_, v___y_236_, v___y_237_, v___y_238_);
if (lean_obj_tag(v___x_241_) == 0)
{
lean_object* v_a_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_249_; 
v_a_242_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_249_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_249_ == 0)
{
v___x_244_ = v___x_241_;
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_a_242_);
lean_dec(v___x_241_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_249_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v___x_247_; 
if (v_isShared_245_ == 0)
{
v___x_247_ = v___x_244_;
goto v_reusejp_246_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v_a_242_);
v___x_247_ = v_reuseFailAlloc_248_;
goto v_reusejp_246_;
}
v_reusejp_246_:
{
return v___x_247_;
}
}
}
else
{
lean_object* v_a_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_257_; 
v_a_250_ = lean_ctor_get(v___x_241_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_241_);
if (v_isSharedCheck_257_ == 0)
{
v___x_252_ = v___x_241_;
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_a_250_);
lean_dec(v___x_241_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_257_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v___x_255_; 
if (v_isShared_253_ == 0)
{
v___x_255_ = v___x_252_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_a_250_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg___boxed(lean_object* v_name_258_, lean_object* v_bi_259_, lean_object* v_type_260_, lean_object* v_k_261_, lean_object* v_kind_262_, lean_object* v___y_263_, lean_object* v___y_264_, lean_object* v___y_265_, lean_object* v___y_266_, lean_object* v___y_267_){
_start:
{
uint8_t v_bi_boxed_268_; uint8_t v_kind_boxed_269_; lean_object* v_res_270_; 
v_bi_boxed_268_ = lean_unbox(v_bi_259_);
v_kind_boxed_269_ = lean_unbox(v_kind_262_);
v_res_270_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_258_, v_bi_boxed_268_, v_type_260_, v_k_261_, v_kind_boxed_269_, v___y_263_, v___y_264_, v___y_265_, v___y_266_);
lean_dec(v___y_266_);
lean_dec_ref(v___y_265_);
lean_dec(v___y_264_);
lean_dec_ref(v___y_263_);
return v_res_270_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(lean_object* v_name_271_, lean_object* v_type_272_, lean_object* v_k_273_, lean_object* v___y_274_, lean_object* v___y_275_, lean_object* v___y_276_, lean_object* v___y_277_){
_start:
{
uint8_t v___x_279_; uint8_t v___x_280_; lean_object* v___x_281_; 
v___x_279_ = 0;
v___x_280_ = 0;
v___x_281_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_271_, v___x_279_, v_type_272_, v_k_273_, v___x_280_, v___y_274_, v___y_275_, v___y_276_, v___y_277_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg___boxed(lean_object* v_name_282_, lean_object* v_type_283_, lean_object* v_k_284_, lean_object* v___y_285_, lean_object* v___y_286_, lean_object* v___y_287_, lean_object* v___y_288_, lean_object* v___y_289_){
_start:
{
lean_object* v_res_290_; 
v_res_290_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_282_, v_type_283_, v_k_284_, v___y_285_, v___y_286_, v___y_287_, v___y_288_);
lean_dec(v___y_288_);
lean_dec_ref(v___y_287_);
lean_dec(v___y_286_);
lean_dec_ref(v___y_285_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed(lean_object* v_xs_298_, lean_object* v_a_299_, lean_object* v_i_300_, lean_object* v_n_301_, lean_object* v_aSizeEqN_302_, lean_object* v_args_303_, lean_object* v_mvarId_304_, lean_object* v_xNamePrefix_305_, lean_object* v_00_u03b1_306_, lean_object* v___x_307_, lean_object* v_xi_308_, lean_object* v___y_309_, lean_object* v___y_310_, lean_object* v___y_311_, lean_object* v___y_312_, lean_object* v___y_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(v_xs_298_, v_a_299_, v_i_300_, v_n_301_, v_aSizeEqN_302_, v_args_303_, v_mvarId_304_, v_xNamePrefix_305_, v_00_u03b1_306_, v___x_307_, v_xi_308_, v___y_309_, v___y_310_, v___y_311_, v___y_312_);
lean_dec(v___y_312_);
lean_dec_ref(v___y_311_);
lean_dec(v___y_310_);
lean_dec_ref(v___y_309_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(lean_object* v_mvarId_315_, lean_object* v_a_316_, lean_object* v_n_317_, lean_object* v_xNamePrefix_318_, lean_object* v_aSizeEqN_319_, lean_object* v_00_u03b1_320_, lean_object* v_i_321_, lean_object* v_xs_322_, lean_object* v_args_323_, lean_object* v_a_324_, lean_object* v_a_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
uint8_t v___x_329_; 
v___x_329_ = lean_nat_dec_lt(v_i_321_, v_n_317_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_i_321_);
lean_dec(v_xNamePrefix_318_);
lean_inc_ref(v_xs_322_);
v___x_330_ = lean_array_to_list(v_xs_322_);
v___x_331_ = l_Lean_Meta_mkArrayLit(v_00_u03b1_320_, v___x_330_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_331_) == 0)
{
lean_object* v_a_332_; lean_object* v___x_333_; 
v_a_332_ = lean_ctor_get(v___x_331_, 0);
lean_inc(v_a_332_);
lean_dec_ref_known(v___x_331_, 1);
lean_inc_ref(v_a_316_);
v___x_333_ = l_Lean_Meta_mkEq(v_a_316_, v_a_332_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_333_) == 0)
{
lean_object* v_a_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; 
v_a_334_ = lean_ctor_get(v___x_333_, 0);
lean_inc(v_a_334_);
lean_dec_ref_known(v___x_333_, 1);
v___x_335_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__1));
v___x_336_ = l_Lean_mkRawNatLit(v_n_317_);
v___x_337_ = lean_unsigned_to_nat(3u);
v___x_338_ = lean_mk_empty_array_with_capacity(v___x_337_);
v___x_339_ = lean_array_push(v___x_338_, v_a_316_);
v___x_340_ = lean_array_push(v___x_339_, v___x_336_);
v___x_341_ = lean_array_push(v___x_340_, v_aSizeEqN_319_);
v___x_342_ = l_Lean_Meta_mkAppM(v___x_335_, v___x_341_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
if (lean_obj_tag(v___x_342_) == 0)
{
lean_object* v_a_343_; lean_object* v___x_344_; lean_object* v___f_345_; lean_object* v___x_346_; lean_object* v___x_347_; 
v_a_343_ = lean_ctor_get(v___x_342_, 0);
lean_inc(v_a_343_);
lean_dec_ref_known(v___x_342_, 1);
v___x_344_ = lean_box(v___x_329_);
v___f_345_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__0___boxed), 11, 5);
lean_closure_set(v___f_345_, 0, v_mvarId_315_);
lean_closure_set(v___f_345_, 1, v_xs_322_);
lean_closure_set(v___f_345_, 2, v___x_344_);
lean_closure_set(v___f_345_, 3, v_args_323_);
lean_closure_set(v___f_345_, 4, v_a_343_);
v___x_346_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___closed__3));
v___x_347_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_346_, v_a_334_, v___f_345_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_347_;
}
else
{
lean_object* v_a_348_; lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_355_; 
lean_dec(v_a_334_);
lean_dec_ref(v_args_323_);
lean_dec_ref(v_xs_322_);
lean_dec(v_mvarId_315_);
v_a_348_ = lean_ctor_get(v___x_342_, 0);
v_isSharedCheck_355_ = !lean_is_exclusive(v___x_342_);
if (v_isSharedCheck_355_ == 0)
{
v___x_350_ = v___x_342_;
v_isShared_351_ = v_isSharedCheck_355_;
goto v_resetjp_349_;
}
else
{
lean_inc(v_a_348_);
lean_dec(v___x_342_);
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
else
{
lean_object* v_a_356_; lean_object* v___x_358_; uint8_t v_isShared_359_; uint8_t v_isSharedCheck_363_; 
lean_dec_ref(v_args_323_);
lean_dec_ref(v_xs_322_);
lean_dec_ref(v_aSizeEqN_319_);
lean_dec(v_n_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_mvarId_315_);
v_a_356_ = lean_ctor_get(v___x_333_, 0);
v_isSharedCheck_363_ = !lean_is_exclusive(v___x_333_);
if (v_isSharedCheck_363_ == 0)
{
v___x_358_ = v___x_333_;
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
else
{
lean_inc(v_a_356_);
lean_dec(v___x_333_);
v___x_358_ = lean_box(0);
v_isShared_359_ = v_isSharedCheck_363_;
goto v_resetjp_357_;
}
v_resetjp_357_:
{
lean_object* v___x_361_; 
if (v_isShared_359_ == 0)
{
v___x_361_ = v___x_358_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_a_356_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
else
{
lean_object* v_a_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_371_; 
lean_dec_ref(v_args_323_);
lean_dec_ref(v_xs_322_);
lean_dec_ref(v_aSizeEqN_319_);
lean_dec(v_n_317_);
lean_dec_ref(v_a_316_);
lean_dec(v_mvarId_315_);
v_a_364_ = lean_ctor_get(v___x_331_, 0);
v_isSharedCheck_371_ = !lean_is_exclusive(v___x_331_);
if (v_isSharedCheck_371_ == 0)
{
v___x_366_ = v___x_331_;
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_a_364_);
lean_dec(v___x_331_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_371_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
lean_object* v___x_369_; 
if (v_isShared_367_ == 0)
{
v___x_369_ = v___x_366_;
goto v_reusejp_368_;
}
else
{
lean_object* v_reuseFailAlloc_370_; 
v_reuseFailAlloc_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_370_, 0, v_a_364_);
v___x_369_ = v_reuseFailAlloc_370_;
goto v_reusejp_368_;
}
v_reusejp_368_:
{
return v___x_369_;
}
}
}
}
else
{
lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___f_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
v___x_372_ = lean_unsigned_to_nat(1u);
v___x_373_ = lean_nat_add(v_i_321_, v___x_372_);
lean_inc(v___x_373_);
lean_inc_ref(v_00_u03b1_320_);
lean_inc(v_xNamePrefix_318_);
v___f_374_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1___boxed), 16, 10);
lean_closure_set(v___f_374_, 0, v_xs_322_);
lean_closure_set(v___f_374_, 1, v_a_316_);
lean_closure_set(v___f_374_, 2, v_i_321_);
lean_closure_set(v___f_374_, 3, v_n_317_);
lean_closure_set(v___f_374_, 4, v_aSizeEqN_319_);
lean_closure_set(v___f_374_, 5, v_args_323_);
lean_closure_set(v___f_374_, 6, v_mvarId_315_);
lean_closure_set(v___f_374_, 7, v_xNamePrefix_318_);
lean_closure_set(v___f_374_, 8, v_00_u03b1_320_);
lean_closure_set(v___f_374_, 9, v___x_373_);
v___x_375_ = lean_name_append_index_after(v_xNamePrefix_318_, v___x_373_);
v___x_376_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v___x_375_, v_00_u03b1_320_, v___f_374_, v_a_324_, v_a_325_, v_a_326_, v_a_327_);
return v___x_376_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___lam__1(lean_object* v_xs_377_, lean_object* v_a_378_, lean_object* v_i_379_, lean_object* v_n_380_, lean_object* v_aSizeEqN_381_, lean_object* v_args_382_, lean_object* v_mvarId_383_, lean_object* v_xNamePrefix_384_, lean_object* v_00_u03b1_385_, lean_object* v___x_386_, lean_object* v_xi_387_, lean_object* v___y_388_, lean_object* v___y_389_, lean_object* v___y_390_, lean_object* v___y_391_){
_start:
{
lean_object* v_xs_393_; lean_object* v___x_394_; 
v_xs_393_ = lean_array_push(v_xs_377_, v_xi_387_);
lean_inc_ref(v_aSizeEqN_381_);
lean_inc(v_n_380_);
lean_inc_ref(v_a_378_);
v___x_394_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_mkArrayGetLit(v_a_378_, v_i_379_, v_n_380_, v_aSizeEqN_381_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
if (lean_obj_tag(v___x_394_) == 0)
{
lean_object* v_a_395_; lean_object* v___x_396_; lean_object* v___x_397_; 
v_a_395_ = lean_ctor_get(v___x_394_, 0);
lean_inc(v_a_395_);
lean_dec_ref_known(v___x_394_, 1);
v___x_396_ = lean_array_push(v_args_382_, v_a_395_);
v___x_397_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_383_, v_a_378_, v_n_380_, v_xNamePrefix_384_, v_aSizeEqN_381_, v_00_u03b1_385_, v___x_386_, v_xs_393_, v___x_396_, v___y_388_, v___y_389_, v___y_390_, v___y_391_);
return v___x_397_;
}
else
{
lean_object* v_a_398_; lean_object* v___x_400_; uint8_t v_isShared_401_; uint8_t v_isSharedCheck_405_; 
lean_dec_ref(v_xs_393_);
lean_dec(v___x_386_);
lean_dec_ref(v_00_u03b1_385_);
lean_dec(v_xNamePrefix_384_);
lean_dec(v_mvarId_383_);
lean_dec_ref(v_args_382_);
lean_dec_ref(v_aSizeEqN_381_);
lean_dec(v_n_380_);
lean_dec_ref(v_a_378_);
v_a_398_ = lean_ctor_get(v___x_394_, 0);
v_isSharedCheck_405_ = !lean_is_exclusive(v___x_394_);
if (v_isSharedCheck_405_ == 0)
{
v___x_400_ = v___x_394_;
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
else
{
lean_inc(v_a_398_);
lean_dec(v___x_394_);
v___x_400_ = lean_box(0);
v_isShared_401_ = v_isSharedCheck_405_;
goto v_resetjp_399_;
}
v_resetjp_399_:
{
lean_object* v___x_403_; 
if (v_isShared_401_ == 0)
{
v___x_403_ = v___x_400_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v_a_398_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop___boxed(lean_object* v_mvarId_406_, lean_object* v_a_407_, lean_object* v_n_408_, lean_object* v_xNamePrefix_409_, lean_object* v_aSizeEqN_410_, lean_object* v_00_u03b1_411_, lean_object* v_i_412_, lean_object* v_xs_413_, lean_object* v_args_414_, lean_object* v_a_415_, lean_object* v_a_416_, lean_object* v_a_417_, lean_object* v_a_418_, lean_object* v_a_419_){
_start:
{
lean_object* v_res_420_; 
v_res_420_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_406_, v_a_407_, v_n_408_, v_xNamePrefix_409_, v_aSizeEqN_410_, v_00_u03b1_411_, v_i_412_, v_xs_413_, v_args_414_, v_a_415_, v_a_416_, v_a_417_, v_a_418_);
lean_dec(v_a_418_);
lean_dec_ref(v_a_417_);
lean_dec(v_a_416_);
lean_dec_ref(v_a_415_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(lean_object* v_00_u03b1_421_, lean_object* v_name_422_, uint8_t v_bi_423_, lean_object* v_type_424_, lean_object* v_k_425_, uint8_t v_kind_426_, lean_object* v___y_427_, lean_object* v___y_428_, lean_object* v___y_429_, lean_object* v___y_430_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___redArg(v_name_422_, v_bi_423_, v_type_424_, v_k_425_, v_kind_426_, v___y_427_, v___y_428_, v___y_429_, v___y_430_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0___boxed(lean_object* v_00_u03b1_433_, lean_object* v_name_434_, lean_object* v_bi_435_, lean_object* v_type_436_, lean_object* v_k_437_, lean_object* v_kind_438_, lean_object* v___y_439_, lean_object* v___y_440_, lean_object* v___y_441_, lean_object* v___y_442_, lean_object* v___y_443_){
_start:
{
uint8_t v_bi_boxed_444_; uint8_t v_kind_boxed_445_; lean_object* v_res_446_; 
v_bi_boxed_444_ = lean_unbox(v_bi_435_);
v_kind_boxed_445_ = lean_unbox(v_kind_438_);
v_res_446_ = l_Lean_Meta_withLocalDecl___at___00Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0_spec__0(v_00_u03b1_433_, v_name_434_, v_bi_boxed_444_, v_type_436_, v_k_437_, v_kind_boxed_445_, v___y_439_, v___y_440_, v___y_441_, v___y_442_);
lean_dec(v___y_442_);
lean_dec_ref(v___y_441_);
lean_dec(v___y_440_);
lean_dec_ref(v___y_439_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(lean_object* v_00_u03b1_447_, lean_object* v_name_448_, lean_object* v_type_449_, lean_object* v_k_450_, lean_object* v___y_451_, lean_object* v___y_452_, lean_object* v___y_453_, lean_object* v___y_454_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___redArg(v_name_448_, v_type_449_, v_k_450_, v___y_451_, v___y_452_, v___y_453_, v___y_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0___boxed(lean_object* v_00_u03b1_457_, lean_object* v_name_458_, lean_object* v_type_459_, lean_object* v_k_460_, lean_object* v___y_461_, lean_object* v___y_462_, lean_object* v___y_463_, lean_object* v___y_464_, lean_object* v___y_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Meta_withLocalDeclD___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop_spec__0(v_00_u03b1_457_, v_name_458_, v_type_459_, v_k_460_, v___y_461_, v___y_462_, v___y_463_, v___y_464_);
lean_dec(v___y_464_);
lean_dec_ref(v___y_463_);
lean_dec(v___y_462_);
lean_dec_ref(v___y_461_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v_ks_471_; lean_object* v_vs_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_496_; 
v_ks_471_ = lean_ctor_get(v_x_467_, 0);
v_vs_472_ = lean_ctor_get(v_x_467_, 1);
v_isSharedCheck_496_ = !lean_is_exclusive(v_x_467_);
if (v_isSharedCheck_496_ == 0)
{
v___x_474_ = v_x_467_;
v_isShared_475_ = v_isSharedCheck_496_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_vs_472_);
lean_inc(v_ks_471_);
lean_dec(v_x_467_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_496_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; uint8_t v___x_477_; 
v___x_476_ = lean_array_get_size(v_ks_471_);
v___x_477_ = lean_nat_dec_lt(v_x_468_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_481_; 
lean_dec(v_x_468_);
v___x_478_ = lean_array_push(v_ks_471_, v_x_469_);
v___x_479_ = lean_array_push(v_vs_472_, v_x_470_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_479_);
lean_ctor_set(v___x_474_, 0, v___x_478_);
v___x_481_ = v___x_474_;
goto v_reusejp_480_;
}
else
{
lean_object* v_reuseFailAlloc_482_; 
v_reuseFailAlloc_482_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_482_, 0, v___x_478_);
lean_ctor_set(v_reuseFailAlloc_482_, 1, v___x_479_);
v___x_481_ = v_reuseFailAlloc_482_;
goto v_reusejp_480_;
}
v_reusejp_480_:
{
return v___x_481_;
}
}
else
{
lean_object* v_k_x27_483_; uint8_t v___x_484_; 
v_k_x27_483_ = lean_array_fget_borrowed(v_ks_471_, v_x_468_);
v___x_484_ = l_Lean_instBEqMVarId_beq(v_x_469_, v_k_x27_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_486_; 
if (v_isShared_475_ == 0)
{
v___x_486_ = v___x_474_;
goto v_reusejp_485_;
}
else
{
lean_object* v_reuseFailAlloc_490_; 
v_reuseFailAlloc_490_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_490_, 0, v_ks_471_);
lean_ctor_set(v_reuseFailAlloc_490_, 1, v_vs_472_);
v___x_486_ = v_reuseFailAlloc_490_;
goto v_reusejp_485_;
}
v_reusejp_485_:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = lean_unsigned_to_nat(1u);
v___x_488_ = lean_nat_add(v_x_468_, v___x_487_);
lean_dec(v_x_468_);
v_x_467_ = v___x_486_;
v_x_468_ = v___x_488_;
goto _start;
}
}
else
{
lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_494_; 
v___x_491_ = lean_array_fset(v_ks_471_, v_x_468_, v_x_469_);
v___x_492_ = lean_array_fset(v_vs_472_, v_x_468_, v_x_470_);
lean_dec(v_x_468_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v___x_492_);
lean_ctor_set(v___x_474_, 0, v___x_491_);
v___x_494_ = v___x_474_;
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
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_n_497_, lean_object* v_k_498_, lean_object* v_v_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = lean_unsigned_to_nat(0u);
v___x_501_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_n_497_, v___x_500_, v_k_498_, v_v_499_);
return v___x_501_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0(void){
_start:
{
lean_object* v___x_502_; 
v___x_502_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(lean_object* v_x_503_, size_t v_x_504_, size_t v_x_505_, lean_object* v_x_506_, lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
lean_object* v_es_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v_j_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_es_508_ = lean_ctor_get(v_x_503_, 0);
v___x_509_ = ((size_t)31ULL);
v___x_510_ = lean_usize_land(v_x_504_, v___x_509_);
v_j_511_ = lean_usize_to_nat(v___x_510_);
v___x_512_ = lean_array_get_size(v_es_508_);
v___x_513_ = lean_nat_dec_lt(v_j_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_dec(v_j_511_);
lean_dec(v_x_507_);
lean_dec(v_x_506_);
return v_x_503_;
}
else
{
lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_552_; 
lean_inc_ref(v_es_508_);
v_isSharedCheck_552_ = !lean_is_exclusive(v_x_503_);
if (v_isSharedCheck_552_ == 0)
{
lean_object* v_unused_553_; 
v_unused_553_ = lean_ctor_get(v_x_503_, 0);
lean_dec(v_unused_553_);
v___x_515_ = v_x_503_;
v_isShared_516_ = v_isSharedCheck_552_;
goto v_resetjp_514_;
}
else
{
lean_dec(v_x_503_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_552_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_v_517_; lean_object* v___x_518_; lean_object* v_xs_x27_519_; lean_object* v___y_521_; 
v_v_517_ = lean_array_fget(v_es_508_, v_j_511_);
v___x_518_ = lean_box(0);
v_xs_x27_519_ = lean_array_fset(v_es_508_, v_j_511_, v___x_518_);
switch(lean_obj_tag(v_v_517_))
{
case 0:
{
lean_object* v_key_526_; lean_object* v_val_527_; lean_object* v___x_529_; uint8_t v_isShared_530_; uint8_t v_isSharedCheck_537_; 
v_key_526_ = lean_ctor_get(v_v_517_, 0);
v_val_527_ = lean_ctor_get(v_v_517_, 1);
v_isSharedCheck_537_ = !lean_is_exclusive(v_v_517_);
if (v_isSharedCheck_537_ == 0)
{
v___x_529_ = v_v_517_;
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
else
{
lean_inc(v_val_527_);
lean_inc(v_key_526_);
lean_dec(v_v_517_);
v___x_529_ = lean_box(0);
v_isShared_530_ = v_isSharedCheck_537_;
goto v_resetjp_528_;
}
v_resetjp_528_:
{
uint8_t v___x_531_; 
v___x_531_ = l_Lean_instBEqMVarId_beq(v_x_506_, v_key_526_);
if (v___x_531_ == 0)
{
lean_object* v___x_532_; lean_object* v___x_533_; 
lean_del_object(v___x_529_);
v___x_532_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_526_, v_val_527_, v_x_506_, v_x_507_);
v___x_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_533_, 0, v___x_532_);
v___y_521_ = v___x_533_;
goto v___jp_520_;
}
else
{
lean_object* v___x_535_; 
lean_dec(v_val_527_);
lean_dec(v_key_526_);
if (v_isShared_530_ == 0)
{
lean_ctor_set(v___x_529_, 1, v_x_507_);
lean_ctor_set(v___x_529_, 0, v_x_506_);
v___x_535_ = v___x_529_;
goto v_reusejp_534_;
}
else
{
lean_object* v_reuseFailAlloc_536_; 
v_reuseFailAlloc_536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_536_, 0, v_x_506_);
lean_ctor_set(v_reuseFailAlloc_536_, 1, v_x_507_);
v___x_535_ = v_reuseFailAlloc_536_;
goto v_reusejp_534_;
}
v_reusejp_534_:
{
v___y_521_ = v___x_535_;
goto v___jp_520_;
}
}
}
}
case 1:
{
lean_object* v_node_538_; lean_object* v___x_540_; uint8_t v_isShared_541_; uint8_t v_isSharedCheck_550_; 
v_node_538_ = lean_ctor_get(v_v_517_, 0);
v_isSharedCheck_550_ = !lean_is_exclusive(v_v_517_);
if (v_isSharedCheck_550_ == 0)
{
v___x_540_ = v_v_517_;
v_isShared_541_ = v_isSharedCheck_550_;
goto v_resetjp_539_;
}
else
{
lean_inc(v_node_538_);
lean_dec(v_v_517_);
v___x_540_ = lean_box(0);
v_isShared_541_ = v_isSharedCheck_550_;
goto v_resetjp_539_;
}
v_resetjp_539_:
{
size_t v___x_542_; size_t v___x_543_; size_t v___x_544_; size_t v___x_545_; lean_object* v___x_546_; lean_object* v___x_548_; 
v___x_542_ = ((size_t)5ULL);
v___x_543_ = lean_usize_shift_right(v_x_504_, v___x_542_);
v___x_544_ = ((size_t)1ULL);
v___x_545_ = lean_usize_add(v_x_505_, v___x_544_);
v___x_546_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_node_538_, v___x_543_, v___x_545_, v_x_506_, v_x_507_);
if (v_isShared_541_ == 0)
{
lean_ctor_set(v___x_540_, 0, v___x_546_);
v___x_548_ = v___x_540_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v___x_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
v___y_521_ = v___x_548_;
goto v___jp_520_;
}
}
}
default: 
{
lean_object* v___x_551_; 
v___x_551_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_551_, 0, v_x_506_);
lean_ctor_set(v___x_551_, 1, v_x_507_);
v___y_521_ = v___x_551_;
goto v___jp_520_;
}
}
v___jp_520_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_array_fset(v_xs_x27_519_, v_j_511_, v___y_521_);
lean_dec(v_j_511_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_522_);
v___x_524_ = v___x_515_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
else
{
lean_object* v_ks_554_; lean_object* v_vs_555_; lean_object* v___x_557_; uint8_t v_isShared_558_; uint8_t v_isSharedCheck_573_; 
v_ks_554_ = lean_ctor_get(v_x_503_, 0);
v_vs_555_ = lean_ctor_get(v_x_503_, 1);
v_isSharedCheck_573_ = !lean_is_exclusive(v_x_503_);
if (v_isSharedCheck_573_ == 0)
{
v___x_557_ = v_x_503_;
v_isShared_558_ = v_isSharedCheck_573_;
goto v_resetjp_556_;
}
else
{
lean_inc(v_vs_555_);
lean_inc(v_ks_554_);
lean_dec(v_x_503_);
v___x_557_ = lean_box(0);
v_isShared_558_ = v_isSharedCheck_573_;
goto v_resetjp_556_;
}
v_resetjp_556_:
{
lean_object* v___x_560_; 
if (v_isShared_558_ == 0)
{
v___x_560_ = v___x_557_;
goto v_reusejp_559_;
}
else
{
lean_object* v_reuseFailAlloc_572_; 
v_reuseFailAlloc_572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_572_, 0, v_ks_554_);
lean_ctor_set(v_reuseFailAlloc_572_, 1, v_vs_555_);
v___x_560_ = v_reuseFailAlloc_572_;
goto v_reusejp_559_;
}
v_reusejp_559_:
{
lean_object* v_newNode_561_; size_t v___x_562_; uint8_t v___x_563_; 
v_newNode_561_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v___x_560_, v_x_506_, v_x_507_);
v___x_562_ = ((size_t)7ULL);
v___x_563_ = lean_usize_dec_le(v___x_562_, v_x_505_);
if (v___x_563_ == 0)
{
lean_object* v___x_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v___x_564_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_561_);
v___x_565_ = lean_unsigned_to_nat(4u);
v___x_566_ = lean_nat_dec_lt(v___x_564_, v___x_565_);
lean_dec(v___x_564_);
if (v___x_566_ == 0)
{
lean_object* v_ks_567_; lean_object* v_vs_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v_ks_567_ = lean_ctor_get(v_newNode_561_, 0);
lean_inc_ref(v_ks_567_);
v_vs_568_ = lean_ctor_get(v_newNode_561_, 1);
lean_inc_ref(v_vs_568_);
lean_dec_ref(v_newNode_561_);
v___x_569_ = lean_unsigned_to_nat(0u);
v___x_570_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___closed__0);
v___x_571_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_x_505_, v_ks_567_, v_vs_568_, v___x_569_, v___x_570_);
lean_dec_ref(v_vs_568_);
lean_dec_ref(v_ks_567_);
return v___x_571_;
}
else
{
return v_newNode_561_;
}
}
else
{
return v_newNode_561_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(size_t v_depth_574_, lean_object* v_keys_575_, lean_object* v_vals_576_, lean_object* v_i_577_, lean_object* v_entries_578_){
_start:
{
lean_object* v___x_579_; uint8_t v___x_580_; 
v___x_579_ = lean_array_get_size(v_keys_575_);
v___x_580_ = lean_nat_dec_lt(v_i_577_, v___x_579_);
if (v___x_580_ == 0)
{
lean_dec(v_i_577_);
return v_entries_578_;
}
else
{
lean_object* v_k_581_; lean_object* v_v_582_; uint64_t v___x_583_; size_t v_h_584_; size_t v___x_585_; lean_object* v___x_586_; size_t v___x_587_; size_t v___x_588_; size_t v___x_589_; size_t v_h_590_; lean_object* v___x_591_; lean_object* v___x_592_; 
v_k_581_ = lean_array_fget_borrowed(v_keys_575_, v_i_577_);
v_v_582_ = lean_array_fget_borrowed(v_vals_576_, v_i_577_);
v___x_583_ = l_Lean_instHashableMVarId_hash(v_k_581_);
v_h_584_ = lean_uint64_to_usize(v___x_583_);
v___x_585_ = ((size_t)5ULL);
v___x_586_ = lean_unsigned_to_nat(1u);
v___x_587_ = ((size_t)1ULL);
v___x_588_ = lean_usize_sub(v_depth_574_, v___x_587_);
v___x_589_ = lean_usize_mul(v___x_585_, v___x_588_);
v_h_590_ = lean_usize_shift_right(v_h_584_, v___x_589_);
v___x_591_ = lean_nat_add(v_i_577_, v___x_586_);
lean_dec(v_i_577_);
lean_inc(v_v_582_);
lean_inc(v_k_581_);
v___x_592_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_entries_578_, v_h_590_, v_depth_574_, v_k_581_, v_v_582_);
v_i_577_ = v___x_591_;
v_entries_578_ = v___x_592_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg___boxed(lean_object* v_depth_594_, lean_object* v_keys_595_, lean_object* v_vals_596_, lean_object* v_i_597_, lean_object* v_entries_598_){
_start:
{
size_t v_depth_boxed_599_; lean_object* v_res_600_; 
v_depth_boxed_599_ = lean_unbox_usize(v_depth_594_);
lean_dec(v_depth_594_);
v_res_600_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_boxed_599_, v_keys_595_, v_vals_596_, v_i_597_, v_entries_598_);
lean_dec_ref(v_vals_596_);
lean_dec_ref(v_keys_595_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_601_, lean_object* v_x_602_, lean_object* v_x_603_, lean_object* v_x_604_, lean_object* v_x_605_){
_start:
{
size_t v_x_999__boxed_606_; size_t v_x_1000__boxed_607_; lean_object* v_res_608_; 
v_x_999__boxed_606_ = lean_unbox_usize(v_x_602_);
lean_dec(v_x_602_);
v_x_1000__boxed_607_ = lean_unbox_usize(v_x_603_);
lean_dec(v_x_603_);
v_res_608_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_601_, v_x_999__boxed_606_, v_x_1000__boxed_607_, v_x_604_, v_x_605_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(lean_object* v_x_609_, lean_object* v_x_610_, lean_object* v_x_611_){
_start:
{
uint64_t v___x_612_; size_t v___x_613_; size_t v___x_614_; lean_object* v___x_615_; 
v___x_612_ = l_Lean_instHashableMVarId_hash(v_x_610_);
v___x_613_ = lean_uint64_to_usize(v___x_612_);
v___x_614_ = ((size_t)1ULL);
v___x_615_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_609_, v___x_613_, v___x_614_, v_x_610_, v_x_611_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(lean_object* v_mvarId_616_, lean_object* v_val_617_, lean_object* v___y_618_){
_start:
{
lean_object* v___x_620_; lean_object* v_mctx_621_; lean_object* v_cache_622_; lean_object* v_zetaDeltaFVarIds_623_; lean_object* v_postponed_624_; lean_object* v_diag_625_; lean_object* v___x_627_; uint8_t v_isShared_628_; uint8_t v_isSharedCheck_655_; 
v___x_620_ = lean_st_ref_take(v___y_618_);
v_mctx_621_ = lean_ctor_get(v___x_620_, 0);
v_cache_622_ = lean_ctor_get(v___x_620_, 1);
v_zetaDeltaFVarIds_623_ = lean_ctor_get(v___x_620_, 2);
v_postponed_624_ = lean_ctor_get(v___x_620_, 3);
v_diag_625_ = lean_ctor_get(v___x_620_, 4);
v_isSharedCheck_655_ = !lean_is_exclusive(v___x_620_);
if (v_isSharedCheck_655_ == 0)
{
v___x_627_ = v___x_620_;
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
else
{
lean_inc(v_diag_625_);
lean_inc(v_postponed_624_);
lean_inc(v_zetaDeltaFVarIds_623_);
lean_inc(v_cache_622_);
lean_inc(v_mctx_621_);
lean_dec(v___x_620_);
v___x_627_ = lean_box(0);
v_isShared_628_ = v_isSharedCheck_655_;
goto v_resetjp_626_;
}
v_resetjp_626_:
{
lean_object* v_depth_629_; lean_object* v_levelAssignDepth_630_; lean_object* v_lmvarCounter_631_; lean_object* v_mvarCounter_632_; lean_object* v_lDecls_633_; lean_object* v_decls_634_; lean_object* v_userNames_635_; lean_object* v_lAssignment_636_; lean_object* v_eAssignment_637_; lean_object* v_dAssignment_638_; lean_object* v_instanceTypedMVars_639_; lean_object* v_synthNormMemo_640_; lean_object* v___x_642_; uint8_t v_isShared_643_; uint8_t v_isSharedCheck_654_; 
v_depth_629_ = lean_ctor_get(v_mctx_621_, 0);
v_levelAssignDepth_630_ = lean_ctor_get(v_mctx_621_, 1);
v_lmvarCounter_631_ = lean_ctor_get(v_mctx_621_, 2);
v_mvarCounter_632_ = lean_ctor_get(v_mctx_621_, 3);
v_lDecls_633_ = lean_ctor_get(v_mctx_621_, 4);
v_decls_634_ = lean_ctor_get(v_mctx_621_, 5);
v_userNames_635_ = lean_ctor_get(v_mctx_621_, 6);
v_lAssignment_636_ = lean_ctor_get(v_mctx_621_, 7);
v_eAssignment_637_ = lean_ctor_get(v_mctx_621_, 8);
v_dAssignment_638_ = lean_ctor_get(v_mctx_621_, 9);
v_instanceTypedMVars_639_ = lean_ctor_get(v_mctx_621_, 10);
v_synthNormMemo_640_ = lean_ctor_get(v_mctx_621_, 11);
v_isSharedCheck_654_ = !lean_is_exclusive(v_mctx_621_);
if (v_isSharedCheck_654_ == 0)
{
v___x_642_ = v_mctx_621_;
v_isShared_643_ = v_isSharedCheck_654_;
goto v_resetjp_641_;
}
else
{
lean_inc(v_synthNormMemo_640_);
lean_inc(v_instanceTypedMVars_639_);
lean_inc(v_dAssignment_638_);
lean_inc(v_eAssignment_637_);
lean_inc(v_lAssignment_636_);
lean_inc(v_userNames_635_);
lean_inc(v_decls_634_);
lean_inc(v_lDecls_633_);
lean_inc(v_mvarCounter_632_);
lean_inc(v_lmvarCounter_631_);
lean_inc(v_levelAssignDepth_630_);
lean_inc(v_depth_629_);
lean_dec(v_mctx_621_);
v___x_642_ = lean_box(0);
v_isShared_643_ = v_isSharedCheck_654_;
goto v_resetjp_641_;
}
v_resetjp_641_:
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_647_; 
v___x_644_ = lean_box(0);
v___x_645_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_eAssignment_637_, v_mvarId_616_, v_val_617_);
if (v_isShared_643_ == 0)
{
lean_ctor_set(v___x_642_, 8, v___x_645_);
v___x_647_ = v___x_642_;
goto v_reusejp_646_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v_depth_629_);
lean_ctor_set(v_reuseFailAlloc_653_, 1, v_levelAssignDepth_630_);
lean_ctor_set(v_reuseFailAlloc_653_, 2, v_lmvarCounter_631_);
lean_ctor_set(v_reuseFailAlloc_653_, 3, v_mvarCounter_632_);
lean_ctor_set(v_reuseFailAlloc_653_, 4, v_lDecls_633_);
lean_ctor_set(v_reuseFailAlloc_653_, 5, v_decls_634_);
lean_ctor_set(v_reuseFailAlloc_653_, 6, v_userNames_635_);
lean_ctor_set(v_reuseFailAlloc_653_, 7, v_lAssignment_636_);
lean_ctor_set(v_reuseFailAlloc_653_, 8, v___x_645_);
lean_ctor_set(v_reuseFailAlloc_653_, 9, v_dAssignment_638_);
lean_ctor_set(v_reuseFailAlloc_653_, 10, v_instanceTypedMVars_639_);
lean_ctor_set(v_reuseFailAlloc_653_, 11, v_synthNormMemo_640_);
v___x_647_ = v_reuseFailAlloc_653_;
goto v_reusejp_646_;
}
v_reusejp_646_:
{
lean_object* v___x_649_; 
if (v_isShared_628_ == 0)
{
lean_ctor_set(v___x_627_, 0, v___x_647_);
v___x_649_ = v___x_627_;
goto v_reusejp_648_;
}
else
{
lean_object* v_reuseFailAlloc_652_; 
v_reuseFailAlloc_652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_652_, 0, v___x_647_);
lean_ctor_set(v_reuseFailAlloc_652_, 1, v_cache_622_);
lean_ctor_set(v_reuseFailAlloc_652_, 2, v_zetaDeltaFVarIds_623_);
lean_ctor_set(v_reuseFailAlloc_652_, 3, v_postponed_624_);
lean_ctor_set(v_reuseFailAlloc_652_, 4, v_diag_625_);
v___x_649_ = v_reuseFailAlloc_652_;
goto v_reusejp_648_;
}
v_reusejp_648_:
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_st_ref_put(v___y_618_, v___x_649_);
v___x_651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_651_, 0, v___x_644_);
return v___x_651_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg___boxed(lean_object* v_mvarId_656_, lean_object* v_val_657_, lean_object* v___y_658_, lean_object* v___y_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_656_, v_val_657_, v___y_658_);
lean_dec(v___y_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(lean_object* v_mvarId_663_, lean_object* v_a_664_, lean_object* v_n_665_, lean_object* v_xNamePrefix_666_, lean_object* v_aSizeEqN_667_, lean_object* v_a_668_, lean_object* v_a_669_, lean_object* v_a_670_, lean_object* v_a_671_){
_start:
{
lean_object* v___x_673_; 
lean_inc_ref(v_a_664_);
v___x_673_ = l_Lean_Meta_getArrayArgType(v_a_664_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_673_) == 0)
{
lean_object* v_a_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v_a_674_ = lean_ctor_get(v___x_673_, 0);
lean_inc(v_a_674_);
lean_dec_ref_known(v___x_673_, 1);
v___x_675_ = lean_unsigned_to_nat(0u);
v___x_676_ = ((lean_object*)(l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___closed__0));
lean_inc(v_mvarId_663_);
v___x_677_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_loop(v_mvarId_663_, v_a_664_, v_n_665_, v_xNamePrefix_666_, v_aSizeEqN_667_, v_a_674_, v___x_675_, v___x_676_, v___x_676_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_677_) == 0)
{
lean_object* v_a_678_; lean_object* v_fst_679_; lean_object* v_snd_680_; lean_object* v___x_681_; 
v_a_678_ = lean_ctor_get(v___x_677_, 0);
lean_inc(v_a_678_);
lean_dec_ref_known(v___x_677_, 1);
v_fst_679_ = lean_ctor_get(v_a_678_, 0);
lean_inc(v_fst_679_);
v_snd_680_ = lean_ctor_get(v_a_678_, 1);
lean_inc(v_snd_680_);
lean_dec(v_a_678_);
lean_inc(v_mvarId_663_);
v___x_681_ = l_Lean_MVarId_getTag(v_mvarId_663_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_681_) == 0)
{
lean_object* v_a_682_; lean_object* v___x_683_; 
v_a_682_ = lean_ctor_get(v___x_681_, 0);
lean_inc(v_a_682_);
lean_dec_ref_known(v___x_681_, 1);
v___x_683_ = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(v_fst_679_, v_a_682_, v_a_668_, v_a_669_, v_a_670_, v_a_671_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_object* v_a_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_694_; 
v_a_684_ = lean_ctor_get(v___x_683_, 0);
lean_inc_n(v_a_684_, 2);
lean_dec_ref_known(v___x_683_, 1);
v___x_685_ = l_Lean_mkAppN(v_a_684_, v_snd_680_);
lean_dec(v_snd_680_);
v___x_686_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_663_, v___x_685_, v_a_669_);
v_isSharedCheck_694_ = !lean_is_exclusive(v___x_686_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v___x_686_, 0);
lean_dec(v_unused_695_);
v___x_688_ = v___x_686_;
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
else
{
lean_dec(v___x_686_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_694_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v___x_690_; lean_object* v___x_692_; 
v___x_690_ = l_Lean_Expr_mvarId_x21(v_a_684_);
lean_dec(v_a_684_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_690_);
v___x_692_ = v___x_688_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
else
{
lean_object* v_a_696_; lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_703_; 
lean_dec(v_snd_680_);
lean_dec(v_mvarId_663_);
v_a_696_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_703_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_703_ == 0)
{
v___x_698_ = v___x_683_;
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
else
{
lean_inc(v_a_696_);
lean_dec(v___x_683_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_703_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_701_; 
if (v_isShared_699_ == 0)
{
v___x_701_ = v___x_698_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_a_696_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
return v___x_701_;
}
}
}
}
else
{
lean_object* v_a_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_711_; 
lean_dec(v_snd_680_);
lean_dec(v_fst_679_);
lean_dec(v_mvarId_663_);
v_a_704_ = lean_ctor_get(v___x_681_, 0);
v_isSharedCheck_711_ = !lean_is_exclusive(v___x_681_);
if (v_isSharedCheck_711_ == 0)
{
v___x_706_ = v___x_681_;
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_a_704_);
lean_dec(v___x_681_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_711_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v___x_709_; 
if (v_isShared_707_ == 0)
{
v___x_709_ = v___x_706_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_a_704_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
return v___x_709_;
}
}
}
}
else
{
lean_object* v_a_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_719_; 
lean_dec(v_mvarId_663_);
v_a_712_ = lean_ctor_get(v___x_677_, 0);
v_isSharedCheck_719_ = !lean_is_exclusive(v___x_677_);
if (v_isSharedCheck_719_ == 0)
{
v___x_714_ = v___x_677_;
v_isShared_715_ = v_isSharedCheck_719_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_a_712_);
lean_dec(v___x_677_);
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
lean_dec_ref(v_aSizeEqN_667_);
lean_dec(v_xNamePrefix_666_);
lean_dec(v_n_665_);
lean_dec_ref(v_a_664_);
lean_dec(v_mvarId_663_);
v_a_720_ = lean_ctor_get(v___x_673_, 0);
v_isSharedCheck_727_ = !lean_is_exclusive(v___x_673_);
if (v_isSharedCheck_727_ == 0)
{
v___x_722_ = v___x_673_;
v_isShared_723_ = v_isSharedCheck_727_;
goto v_resetjp_721_;
}
else
{
lean_inc(v_a_720_);
lean_dec(v___x_673_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit___boxed(lean_object* v_mvarId_728_, lean_object* v_a_729_, lean_object* v_n_730_, lean_object* v_xNamePrefix_731_, lean_object* v_aSizeEqN_732_, lean_object* v_a_733_, lean_object* v_a_734_, lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v_res_738_; 
v_res_738_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_728_, v_a_729_, v_n_730_, v_xNamePrefix_731_, v_aSizeEqN_732_, v_a_733_, v_a_734_, v_a_735_, v_a_736_);
lean_dec(v_a_736_);
lean_dec_ref(v_a_735_);
lean_dec(v_a_734_);
lean_dec_ref(v_a_733_);
return v_res_738_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(lean_object* v_mvarId_739_, lean_object* v_val_740_, lean_object* v___y_741_, lean_object* v___y_742_, lean_object* v___y_743_, lean_object* v___y_744_){
_start:
{
lean_object* v___x_746_; 
v___x_746_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___redArg(v_mvarId_739_, v_val_740_, v___y_742_);
return v___x_746_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0___boxed(lean_object* v_mvarId_747_, lean_object* v_val_748_, lean_object* v___y_749_, lean_object* v___y_750_, lean_object* v___y_751_, lean_object* v___y_752_, lean_object* v___y_753_){
_start:
{
lean_object* v_res_754_; 
v_res_754_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0(v_mvarId_747_, v_val_748_, v___y_749_, v___y_750_, v___y_751_, v___y_752_);
lean_dec(v___y_752_);
lean_dec_ref(v___y_751_);
lean_dec(v___y_750_);
lean_dec_ref(v___y_749_);
return v_res_754_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0(lean_object* v_00_u03b2_755_, lean_object* v_x_756_, lean_object* v_x_757_, lean_object* v_x_758_){
_start:
{
lean_object* v___x_759_; 
v___x_759_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0___redArg(v_x_756_, v_x_757_, v_x_758_);
return v___x_759_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_760_, lean_object* v_x_761_, size_t v_x_762_, size_t v_x_763_, lean_object* v_x_764_, lean_object* v_x_765_){
_start:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___redArg(v_x_761_, v_x_762_, v_x_763_, v_x_764_, v_x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_767_, lean_object* v_x_768_, lean_object* v_x_769_, lean_object* v_x_770_, lean_object* v_x_771_, lean_object* v_x_772_){
_start:
{
size_t v_x_1355__boxed_773_; size_t v_x_1356__boxed_774_; lean_object* v_res_775_; 
v_x_1355__boxed_773_ = lean_unbox_usize(v_x_769_);
lean_dec(v_x_769_);
v_x_1356__boxed_774_ = lean_unbox_usize(v_x_770_);
lean_dec(v_x_770_);
v_res_775_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1(v_00_u03b2_767_, v_x_768_, v_x_1355__boxed_773_, v_x_1356__boxed_774_, v_x_771_, v_x_772_);
return v_res_775_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_776_, lean_object* v_n_777_, lean_object* v_k_778_, lean_object* v_v_779_){
_start:
{
lean_object* v___x_780_; 
v___x_780_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2___redArg(v_n_777_, v_k_778_, v_v_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(lean_object* v_00_u03b2_781_, size_t v_depth_782_, lean_object* v_keys_783_, lean_object* v_vals_784_, lean_object* v_heq_785_, lean_object* v_i_786_, lean_object* v_entries_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___redArg(v_depth_782_, v_keys_783_, v_vals_784_, v_i_786_, v_entries_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3___boxed(lean_object* v_00_u03b2_789_, lean_object* v_depth_790_, lean_object* v_keys_791_, lean_object* v_vals_792_, lean_object* v_heq_793_, lean_object* v_i_794_, lean_object* v_entries_795_){
_start:
{
size_t v_depth_boxed_796_; lean_object* v_res_797_; 
v_depth_boxed_796_ = lean_unbox_usize(v_depth_790_);
lean_dec(v_depth_790_);
v_res_797_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__3(v_00_u03b2_789_, v_depth_boxed_796_, v_keys_791_, v_vals_792_, v_heq_793_, v_i_794_, v_entries_795_);
lean_dec_ref(v_vals_792_);
lean_dec_ref(v_keys_791_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_798_, lean_object* v_x_799_, lean_object* v_x_800_, lean_object* v_x_801_, lean_object* v_x_802_){
_start:
{
lean_object* v___x_803_; 
v___x_803_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit_spec__0_spec__0_spec__1_spec__2_spec__3___redArg(v_x_799_, v_x_800_, v_x_801_, v_x_802_);
return v___x_803_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(lean_object* v_mvarId_804_, lean_object* v_x_805_, lean_object* v___y_806_, lean_object* v___y_807_, lean_object* v___y_808_, lean_object* v___y_809_){
_start:
{
lean_object* v___x_811_; 
v___x_811_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), v_mvarId_804_, v_x_805_, v___y_806_, v___y_807_, v___y_808_, v___y_809_);
if (lean_obj_tag(v___x_811_) == 0)
{
lean_object* v_a_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_819_; 
v_a_812_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_819_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_819_ == 0)
{
v___x_814_ = v___x_811_;
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_a_812_);
lean_dec(v___x_811_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_819_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_817_; 
if (v_isShared_815_ == 0)
{
v___x_817_ = v___x_814_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_818_; 
v_reuseFailAlloc_818_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_818_, 0, v_a_812_);
v___x_817_ = v_reuseFailAlloc_818_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
return v___x_817_;
}
}
}
else
{
lean_object* v_a_820_; lean_object* v___x_822_; uint8_t v_isShared_823_; uint8_t v_isSharedCheck_827_; 
v_a_820_ = lean_ctor_get(v___x_811_, 0);
v_isSharedCheck_827_ = !lean_is_exclusive(v___x_811_);
if (v_isSharedCheck_827_ == 0)
{
v___x_822_ = v___x_811_;
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
else
{
lean_inc(v_a_820_);
lean_dec(v___x_811_);
v___x_822_ = lean_box(0);
v_isShared_823_ = v_isSharedCheck_827_;
goto v_resetjp_821_;
}
v_resetjp_821_:
{
lean_object* v___x_825_; 
if (v_isShared_823_ == 0)
{
v___x_825_ = v___x_822_;
goto v_reusejp_824_;
}
else
{
lean_object* v_reuseFailAlloc_826_; 
v_reuseFailAlloc_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_826_, 0, v_a_820_);
v___x_825_ = v_reuseFailAlloc_826_;
goto v_reusejp_824_;
}
v_reusejp_824_:
{
return v___x_825_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg___boxed(lean_object* v_mvarId_828_, lean_object* v_x_829_, lean_object* v___y_830_, lean_object* v___y_831_, lean_object* v___y_832_, lean_object* v___y_833_, lean_object* v___y_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_828_, v_x_829_, v___y_830_, v___y_831_, v___y_832_, v___y_833_);
lean_dec(v___y_833_);
lean_dec_ref(v___y_832_);
lean_dec(v___y_831_);
lean_dec_ref(v___y_830_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(lean_object* v_00_u03b1_836_, lean_object* v_mvarId_837_, lean_object* v_x_838_, lean_object* v___y_839_, lean_object* v___y_840_, lean_object* v___y_841_, lean_object* v___y_842_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_837_, v_x_838_, v___y_839_, v___y_840_, v___y_841_, v___y_842_);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___boxed(lean_object* v_00_u03b1_845_, lean_object* v_mvarId_846_, lean_object* v_x_847_, lean_object* v___y_848_, lean_object* v___y_849_, lean_object* v___y_850_, lean_object* v___y_851_, lean_object* v___y_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2(v_00_u03b1_845_, v_mvarId_846_, v_x_847_, v___y_848_, v___y_849_, v___y_850_, v___y_851_);
lean_dec(v___y_851_);
lean_dec_ref(v___y_850_);
lean_dec(v___y_849_);
lean_dec_ref(v___y_848_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(size_t v_sz_854_, size_t v_i_855_, lean_object* v_bs_856_){
_start:
{
uint8_t v___x_857_; 
v___x_857_ = lean_usize_dec_lt(v_i_855_, v_sz_854_);
if (v___x_857_ == 0)
{
return v_bs_856_;
}
else
{
lean_object* v_v_858_; lean_object* v___x_859_; lean_object* v_bs_x27_860_; lean_object* v___x_861_; size_t v___x_862_; size_t v___x_863_; lean_object* v___x_864_; 
v_v_858_ = lean_array_uget(v_bs_856_, v_i_855_);
v___x_859_ = lean_unsigned_to_nat(0u);
v_bs_x27_860_ = lean_array_uset(v_bs_856_, v_i_855_, v___x_859_);
v___x_861_ = l_Lean_mkRawNatLit(v_v_858_);
v___x_862_ = ((size_t)1ULL);
v___x_863_ = lean_usize_add(v_i_855_, v___x_862_);
v___x_864_ = lean_array_uset(v_bs_x27_860_, v_i_855_, v___x_861_);
v_i_855_ = v___x_863_;
v_bs_856_ = v___x_864_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0___boxed(lean_object* v_sz_866_, lean_object* v_i_867_, lean_object* v_bs_868_){
_start:
{
size_t v_sz_boxed_869_; size_t v_i_boxed_870_; lean_object* v_res_871_; 
v_sz_boxed_869_ = lean_unbox_usize(v_sz_866_);
lean_dec(v_sz_866_);
v_i_boxed_870_ = lean_unbox_usize(v_i_867_);
lean_dec(v_i_867_);
v_res_871_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_boxed_869_, v_i_boxed_870_, v_bs_868_);
return v_res_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(lean_object* v___x_872_, lean_object* v_mvarId_873_, lean_object* v_a_874_, lean_object* v___x_875_, lean_object* v_xNamePrefix_876_, lean_object* v___x_877_, lean_object* v_subst_878_, uint8_t v___x_879_, lean_object* v___y_880_, lean_object* v___y_881_, lean_object* v___y_882_, lean_object* v___y_883_){
_start:
{
lean_object* v___x_885_; 
v___x_885_ = l_Lean_Meta_mkEqSymm(v___x_872_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v_a_886_; lean_object* v___x_887_; 
v_a_886_ = lean_ctor_get(v___x_885_, 0);
lean_inc(v_a_886_);
lean_dec_ref_known(v___x_885_, 1);
lean_inc(v___x_875_);
v___x_887_ = l___private_Lean_Meta_Match_CaseArraySizes_0__Lean_Meta_introArrayLit(v_mvarId_873_, v_a_874_, v___x_875_, v_xNamePrefix_876_, v_a_886_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_887_) == 0)
{
lean_object* v_a_888_; lean_object* v___x_889_; uint8_t v___x_890_; lean_object* v___x_891_; 
v_a_888_ = lean_ctor_get(v___x_887_, 0);
lean_inc(v_a_888_);
lean_dec_ref_known(v___x_887_, 1);
v___x_889_ = lean_box(0);
v___x_890_ = 0;
v___x_891_ = l_Lean_Meta_introNCore(v_a_888_, v___x_875_, v___x_889_, v___x_890_, v___x_890_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v_a_892_; lean_object* v_fst_893_; lean_object* v_snd_894_; lean_object* v___x_895_; 
v_a_892_ = lean_ctor_get(v___x_891_, 0);
lean_inc(v_a_892_);
lean_dec_ref_known(v___x_891_, 1);
v_fst_893_ = lean_ctor_get(v_a_892_, 0);
lean_inc(v_fst_893_);
v_snd_894_ = lean_ctor_get(v_a_892_, 1);
lean_inc(v_snd_894_);
lean_dec(v_a_892_);
v___x_895_ = l_Lean_Meta_intro1Core(v_snd_894_, v___x_890_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v_a_896_; lean_object* v_fst_897_; lean_object* v_snd_898_; lean_object* v___x_899_; 
v_a_896_ = lean_ctor_get(v___x_895_, 0);
lean_inc(v_a_896_);
lean_dec_ref_known(v___x_895_, 1);
v_fst_897_ = lean_ctor_get(v_a_896_, 0);
lean_inc(v_fst_897_);
v_snd_898_ = lean_ctor_get(v_a_896_, 1);
lean_inc(v_snd_898_);
lean_dec(v_a_896_);
v___x_899_ = l_Lean_MVarId_clear(v_snd_898_, v___x_877_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v_a_900_; lean_object* v___x_901_; 
v_a_900_ = lean_ctor_get(v___x_899_, 0);
lean_inc(v_a_900_);
lean_dec_ref_known(v___x_899_, 1);
v___x_901_ = l_Lean_Meta_substCore(v_a_900_, v_fst_897_, v___x_890_, v_subst_878_, v___x_879_, v___x_890_, v___y_880_, v___y_881_, v___y_882_, v___y_883_);
if (lean_obj_tag(v___x_901_) == 0)
{
lean_object* v_a_902_; lean_object* v___x_904_; uint8_t v_isShared_905_; uint8_t v_isSharedCheck_913_; 
v_a_902_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_913_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_913_ == 0)
{
v___x_904_ = v___x_901_;
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
else
{
lean_inc(v_a_902_);
lean_dec(v___x_901_);
v___x_904_ = lean_box(0);
v_isShared_905_ = v_isSharedCheck_913_;
goto v_resetjp_903_;
}
v_resetjp_903_:
{
lean_object* v_fst_906_; lean_object* v_snd_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_911_; 
v_fst_906_ = lean_ctor_get(v_a_902_, 0);
lean_inc(v_fst_906_);
v_snd_907_ = lean_ctor_get(v_a_902_, 1);
lean_inc(v_snd_907_);
lean_dec(v_a_902_);
v___x_908_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0));
v___x_909_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_909_, 0, v_snd_907_);
lean_ctor_set(v___x_909_, 1, v_fst_893_);
lean_ctor_set(v___x_909_, 2, v___x_908_);
lean_ctor_set(v___x_909_, 3, v_fst_906_);
if (v_isShared_905_ == 0)
{
lean_ctor_set(v___x_904_, 0, v___x_909_);
v___x_911_ = v___x_904_;
goto v_reusejp_910_;
}
else
{
lean_object* v_reuseFailAlloc_912_; 
v_reuseFailAlloc_912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_912_, 0, v___x_909_);
v___x_911_ = v_reuseFailAlloc_912_;
goto v_reusejp_910_;
}
v_reusejp_910_:
{
return v___x_911_;
}
}
}
else
{
lean_object* v_a_914_; lean_object* v___x_916_; uint8_t v_isShared_917_; uint8_t v_isSharedCheck_921_; 
lean_dec(v_fst_893_);
v_a_914_ = lean_ctor_get(v___x_901_, 0);
v_isSharedCheck_921_ = !lean_is_exclusive(v___x_901_);
if (v_isSharedCheck_921_ == 0)
{
v___x_916_ = v___x_901_;
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
else
{
lean_inc(v_a_914_);
lean_dec(v___x_901_);
v___x_916_ = lean_box(0);
v_isShared_917_ = v_isSharedCheck_921_;
goto v_resetjp_915_;
}
v_resetjp_915_:
{
lean_object* v___x_919_; 
if (v_isShared_917_ == 0)
{
v___x_919_ = v___x_916_;
goto v_reusejp_918_;
}
else
{
lean_object* v_reuseFailAlloc_920_; 
v_reuseFailAlloc_920_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_920_, 0, v_a_914_);
v___x_919_ = v_reuseFailAlloc_920_;
goto v_reusejp_918_;
}
v_reusejp_918_:
{
return v___x_919_;
}
}
}
}
else
{
lean_object* v_a_922_; lean_object* v___x_924_; uint8_t v_isShared_925_; uint8_t v_isSharedCheck_929_; 
lean_dec(v_fst_897_);
lean_dec(v_fst_893_);
lean_dec(v_subst_878_);
v_a_922_ = lean_ctor_get(v___x_899_, 0);
v_isSharedCheck_929_ = !lean_is_exclusive(v___x_899_);
if (v_isSharedCheck_929_ == 0)
{
v___x_924_ = v___x_899_;
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
else
{
lean_inc(v_a_922_);
lean_dec(v___x_899_);
v___x_924_ = lean_box(0);
v_isShared_925_ = v_isSharedCheck_929_;
goto v_resetjp_923_;
}
v_resetjp_923_:
{
lean_object* v___x_927_; 
if (v_isShared_925_ == 0)
{
v___x_927_ = v___x_924_;
goto v_reusejp_926_;
}
else
{
lean_object* v_reuseFailAlloc_928_; 
v_reuseFailAlloc_928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_928_, 0, v_a_922_);
v___x_927_ = v_reuseFailAlloc_928_;
goto v_reusejp_926_;
}
v_reusejp_926_:
{
return v___x_927_;
}
}
}
}
else
{
lean_object* v_a_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_937_; 
lean_dec(v_fst_893_);
lean_dec(v_subst_878_);
lean_dec(v___x_877_);
v_a_930_ = lean_ctor_get(v___x_895_, 0);
v_isSharedCheck_937_ = !lean_is_exclusive(v___x_895_);
if (v_isSharedCheck_937_ == 0)
{
v___x_932_ = v___x_895_;
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_a_930_);
lean_dec(v___x_895_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_937_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_935_; 
if (v_isShared_933_ == 0)
{
v___x_935_ = v___x_932_;
goto v_reusejp_934_;
}
else
{
lean_object* v_reuseFailAlloc_936_; 
v_reuseFailAlloc_936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_936_, 0, v_a_930_);
v___x_935_ = v_reuseFailAlloc_936_;
goto v_reusejp_934_;
}
v_reusejp_934_:
{
return v___x_935_;
}
}
}
}
else
{
lean_object* v_a_938_; lean_object* v___x_940_; uint8_t v_isShared_941_; uint8_t v_isSharedCheck_945_; 
lean_dec(v_subst_878_);
lean_dec(v___x_877_);
v_a_938_ = lean_ctor_get(v___x_891_, 0);
v_isSharedCheck_945_ = !lean_is_exclusive(v___x_891_);
if (v_isSharedCheck_945_ == 0)
{
v___x_940_ = v___x_891_;
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
else
{
lean_inc(v_a_938_);
lean_dec(v___x_891_);
v___x_940_ = lean_box(0);
v_isShared_941_ = v_isSharedCheck_945_;
goto v_resetjp_939_;
}
v_resetjp_939_:
{
lean_object* v___x_943_; 
if (v_isShared_941_ == 0)
{
v___x_943_ = v___x_940_;
goto v_reusejp_942_;
}
else
{
lean_object* v_reuseFailAlloc_944_; 
v_reuseFailAlloc_944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_944_, 0, v_a_938_);
v___x_943_ = v_reuseFailAlloc_944_;
goto v_reusejp_942_;
}
v_reusejp_942_:
{
return v___x_943_;
}
}
}
}
else
{
lean_object* v_a_946_; lean_object* v___x_948_; uint8_t v_isShared_949_; uint8_t v_isSharedCheck_953_; 
lean_dec(v_subst_878_);
lean_dec(v___x_877_);
lean_dec(v___x_875_);
v_a_946_ = lean_ctor_get(v___x_887_, 0);
v_isSharedCheck_953_ = !lean_is_exclusive(v___x_887_);
if (v_isSharedCheck_953_ == 0)
{
v___x_948_ = v___x_887_;
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
else
{
lean_inc(v_a_946_);
lean_dec(v___x_887_);
v___x_948_ = lean_box(0);
v_isShared_949_ = v_isSharedCheck_953_;
goto v_resetjp_947_;
}
v_resetjp_947_:
{
lean_object* v___x_951_; 
if (v_isShared_949_ == 0)
{
v___x_951_ = v___x_948_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v_a_946_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
else
{
lean_object* v_a_954_; lean_object* v___x_956_; uint8_t v_isShared_957_; uint8_t v_isSharedCheck_961_; 
lean_dec(v_subst_878_);
lean_dec(v___x_877_);
lean_dec(v_xNamePrefix_876_);
lean_dec(v___x_875_);
lean_dec_ref(v_a_874_);
lean_dec(v_mvarId_873_);
v_a_954_ = lean_ctor_get(v___x_885_, 0);
v_isSharedCheck_961_ = !lean_is_exclusive(v___x_885_);
if (v_isSharedCheck_961_ == 0)
{
v___x_956_ = v___x_885_;
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
else
{
lean_inc(v_a_954_);
lean_dec(v___x_885_);
v___x_956_ = lean_box(0);
v_isShared_957_ = v_isSharedCheck_961_;
goto v_resetjp_955_;
}
v_resetjp_955_:
{
lean_object* v___x_959_; 
if (v_isShared_957_ == 0)
{
v___x_959_ = v___x_956_;
goto v_reusejp_958_;
}
else
{
lean_object* v_reuseFailAlloc_960_; 
v_reuseFailAlloc_960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_960_, 0, v_a_954_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed(lean_object* v___x_962_, lean_object* v_mvarId_963_, lean_object* v_a_964_, lean_object* v___x_965_, lean_object* v_xNamePrefix_966_, lean_object* v___x_967_, lean_object* v_subst_968_, lean_object* v___x_969_, lean_object* v___y_970_, lean_object* v___y_971_, lean_object* v___y_972_, lean_object* v___y_973_, lean_object* v___y_974_){
_start:
{
uint8_t v___x_3706__boxed_975_; lean_object* v_res_976_; 
v___x_3706__boxed_975_ = lean_unbox(v___x_969_);
v_res_976_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0(v___x_962_, v_mvarId_963_, v_a_964_, v___x_965_, v_xNamePrefix_966_, v___x_967_, v_subst_968_, v___x_3706__boxed_975_, v___y_970_, v___y_971_, v___y_972_, v___y_973_);
lean_dec(v___y_973_);
lean_dec_ref(v___y_972_);
lean_dec(v___y_971_);
lean_dec_ref(v___y_970_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(lean_object* v_fst_977_, size_t v_sz_978_, size_t v_i_979_, lean_object* v_bs_980_){
_start:
{
uint8_t v___x_981_; 
v___x_981_ = lean_usize_dec_lt(v_i_979_, v_sz_978_);
if (v___x_981_ == 0)
{
return v_bs_980_;
}
else
{
lean_object* v_v_982_; lean_object* v___x_983_; lean_object* v_bs_x27_984_; lean_object* v___x_985_; lean_object* v___x_986_; size_t v___x_987_; size_t v___x_988_; lean_object* v___x_989_; 
v_v_982_ = lean_array_uget(v_bs_980_, v_i_979_);
v___x_983_ = lean_unsigned_to_nat(0u);
v_bs_x27_984_ = lean_array_uset(v_bs_980_, v_i_979_, v___x_983_);
v___x_985_ = l_Lean_Meta_FVarSubst_get(v_fst_977_, v_v_982_);
v___x_986_ = l_Lean_Expr_fvarId_x21(v___x_985_);
lean_dec_ref(v___x_985_);
v___x_987_ = ((size_t)1ULL);
v___x_988_ = lean_usize_add(v_i_979_, v___x_987_);
v___x_989_ = lean_array_uset(v_bs_x27_984_, v_i_979_, v___x_986_);
v_i_979_ = v___x_988_;
v_bs_980_ = v___x_989_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1___boxed(lean_object* v_fst_991_, lean_object* v_sz_992_, lean_object* v_i_993_, lean_object* v_bs_994_){
_start:
{
size_t v_sz_boxed_995_; size_t v_i_boxed_996_; lean_object* v_res_997_; 
v_sz_boxed_995_ = lean_unbox_usize(v_sz_992_);
lean_dec(v_sz_992_);
v_i_boxed_996_ = lean_unbox_usize(v_i_993_);
lean_dec(v_i_993_);
v_res_997_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_991_, v_sz_boxed_995_, v_i_boxed_996_, v_bs_994_);
lean_dec(v_fst_991_);
return v_res_997_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(lean_object* v_sizes_998_, lean_object* v_fst_999_, lean_object* v_a_1000_, lean_object* v_xNamePrefix_1001_, size_t v_sz_1002_, size_t v_i_1003_, lean_object* v_bs_1004_, lean_object* v___y_1005_, lean_object* v___y_1006_, lean_object* v___y_1007_, lean_object* v___y_1008_){
_start:
{
uint8_t v___x_1010_; 
v___x_1010_ = lean_usize_dec_lt(v_i_1003_, v_sz_1002_);
if (v___x_1010_ == 0)
{
lean_object* v___x_1011_; 
lean_dec(v_xNamePrefix_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_fst_999_);
v___x_1011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1011_, 0, v_bs_1004_);
return v___x_1011_;
}
else
{
lean_object* v_v_1012_; lean_object* v_mvarId_1013_; lean_object* v_newHs_1014_; lean_object* v_subst_1015_; lean_object* v___x_1016_; lean_object* v_bs_x27_1017_; lean_object* v_a_1019_; lean_object* v___x_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; 
v_v_1012_ = lean_array_uget_borrowed(v_bs_1004_, v_i_1003_);
v_mvarId_1013_ = lean_ctor_get(v_v_1012_, 0);
lean_inc(v_mvarId_1013_);
v_newHs_1014_ = lean_ctor_get(v_v_1012_, 1);
lean_inc_ref(v_newHs_1014_);
v_subst_1015_ = lean_ctor_get(v_v_1012_, 2);
lean_inc(v_subst_1015_);
v___x_1016_ = lean_unsigned_to_nat(0u);
v_bs_x27_1017_ = lean_array_uset(v_bs_1004_, v_i_1003_, v___x_1016_);
v___x_1024_ = lean_usize_to_nat(v_i_1003_);
v___x_1025_ = lean_array_get_size(v_sizes_998_);
v___x_1026_ = lean_nat_dec_lt(v___x_1024_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_dec(v___x_1024_);
lean_inc(v_fst_999_);
v___x_1027_ = l_Lean_Meta_substCore(v_mvarId_1013_, v_fst_999_, v___x_1026_, v_subst_1015_, v___x_1010_, v___x_1026_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1027_) == 0)
{
lean_object* v_a_1028_; lean_object* v_fst_1029_; lean_object* v_snd_1030_; size_t v_sz_1031_; size_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v_a_1028_ = lean_ctor_get(v___x_1027_, 0);
lean_inc(v_a_1028_);
lean_dec_ref_known(v___x_1027_, 1);
v_fst_1029_ = lean_ctor_get(v_a_1028_, 0);
lean_inc(v_fst_1029_);
v_snd_1030_ = lean_ctor_get(v_a_1028_, 1);
lean_inc(v_snd_1030_);
lean_dec(v_a_1028_);
v_sz_1031_ = lean_array_size(v_newHs_1014_);
v___x_1032_ = ((size_t)0ULL);
v___x_1033_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__1(v_fst_1029_, v_sz_1031_, v___x_1032_, v_newHs_1014_);
v___x_1034_ = ((lean_object*)(l_Lean_Meta_instInhabitedCaseArraySizesSubgoal_default___closed__0));
v___x_1035_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1035_, 0, v_snd_1030_);
lean_ctor_set(v___x_1035_, 1, v___x_1034_);
lean_ctor_set(v___x_1035_, 2, v___x_1033_);
lean_ctor_set(v___x_1035_, 3, v_fst_1029_);
v_a_1019_ = v___x_1035_;
goto v___jp_1018_;
}
else
{
lean_object* v_a_1036_; lean_object* v___x_1038_; uint8_t v_isShared_1039_; uint8_t v_isSharedCheck_1043_; 
lean_dec_ref(v_bs_x27_1017_);
lean_dec_ref(v_newHs_1014_);
lean_dec(v_xNamePrefix_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_fst_999_);
v_a_1036_ = lean_ctor_get(v___x_1027_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v___x_1027_);
if (v_isSharedCheck_1043_ == 0)
{
v___x_1038_ = v___x_1027_;
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
else
{
lean_inc(v_a_1036_);
lean_dec(v___x_1027_);
v___x_1038_ = lean_box(0);
v_isShared_1039_ = v_isSharedCheck_1043_;
goto v_resetjp_1037_;
}
v_resetjp_1037_:
{
lean_object* v___x_1041_; 
if (v_isShared_1039_ == 0)
{
v___x_1041_ = v___x_1038_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v_a_1036_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___f_1049_; lean_object* v___x_1050_; 
lean_dec_ref(v_newHs_1014_);
lean_inc(v_fst_999_);
v___x_1044_ = l_Lean_Meta_FVarSubst_get(v_subst_1015_, v_fst_999_);
v___x_1045_ = l_Lean_Expr_fvarId_x21(v___x_1044_);
lean_dec_ref(v___x_1044_);
v___x_1046_ = lean_array_fget_borrowed(v_sizes_998_, v___x_1024_);
lean_dec(v___x_1024_);
lean_inc(v___x_1045_);
v___x_1047_ = l_Lean_mkFVar(v___x_1045_);
v___x_1048_ = lean_box(v___x_1010_);
lean_inc(v_xNamePrefix_1001_);
lean_inc(v___x_1046_);
lean_inc_ref(v_a_1000_);
lean_inc(v_mvarId_1013_);
v___f_1049_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___lam__0___boxed), 13, 8);
lean_closure_set(v___f_1049_, 0, v___x_1047_);
lean_closure_set(v___f_1049_, 1, v_mvarId_1013_);
lean_closure_set(v___f_1049_, 2, v_a_1000_);
lean_closure_set(v___f_1049_, 3, v___x_1046_);
lean_closure_set(v___f_1049_, 4, v_xNamePrefix_1001_);
lean_closure_set(v___f_1049_, 5, v___x_1045_);
lean_closure_set(v___f_1049_, 6, v_subst_1015_);
lean_closure_set(v___f_1049_, 7, v___x_1048_);
v___x_1050_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_1013_, v___f_1049_, v___y_1005_, v___y_1006_, v___y_1007_, v___y_1008_);
if (lean_obj_tag(v___x_1050_) == 0)
{
lean_object* v_a_1051_; 
v_a_1051_ = lean_ctor_get(v___x_1050_, 0);
lean_inc(v_a_1051_);
lean_dec_ref_known(v___x_1050_, 1);
v_a_1019_ = v_a_1051_;
goto v___jp_1018_;
}
else
{
lean_object* v_a_1052_; lean_object* v___x_1054_; uint8_t v_isShared_1055_; uint8_t v_isSharedCheck_1059_; 
lean_dec_ref(v_bs_x27_1017_);
lean_dec(v_xNamePrefix_1001_);
lean_dec_ref(v_a_1000_);
lean_dec(v_fst_999_);
v_a_1052_ = lean_ctor_get(v___x_1050_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1050_);
if (v_isSharedCheck_1059_ == 0)
{
v___x_1054_ = v___x_1050_;
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
else
{
lean_inc(v_a_1052_);
lean_dec(v___x_1050_);
v___x_1054_ = lean_box(0);
v_isShared_1055_ = v_isSharedCheck_1059_;
goto v_resetjp_1053_;
}
v_resetjp_1053_:
{
lean_object* v___x_1057_; 
if (v_isShared_1055_ == 0)
{
v___x_1057_ = v___x_1054_;
goto v_reusejp_1056_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_a_1052_);
v___x_1057_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1056_;
}
v_reusejp_1056_:
{
return v___x_1057_;
}
}
}
}
v___jp_1018_:
{
size_t v___x_1020_; size_t v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((size_t)1ULL);
v___x_1021_ = lean_usize_add(v_i_1003_, v___x_1020_);
v___x_1022_ = lean_array_uset(v_bs_x27_1017_, v_i_1003_, v_a_1019_);
v_i_1003_ = v___x_1021_;
v_bs_1004_ = v___x_1022_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg___boxed(lean_object* v_sizes_1060_, lean_object* v_fst_1061_, lean_object* v_a_1062_, lean_object* v_xNamePrefix_1063_, lean_object* v_sz_1064_, lean_object* v_i_1065_, lean_object* v_bs_1066_, lean_object* v___y_1067_, lean_object* v___y_1068_, lean_object* v___y_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
size_t v_sz_boxed_1072_; size_t v_i_boxed_1073_; lean_object* v_res_1074_; 
v_sz_boxed_1072_ = lean_unbox_usize(v_sz_1064_);
lean_dec(v_sz_1064_);
v_i_boxed_1073_ = lean_unbox_usize(v_i_1065_);
lean_dec(v_i_1065_);
v_res_1074_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1060_, v_fst_1061_, v_a_1062_, v_xNamePrefix_1063_, v_sz_boxed_1072_, v_i_boxed_1073_, v_bs_1066_, v___y_1067_, v___y_1068_, v___y_1069_, v___y_1070_);
lean_dec(v___y_1070_);
lean_dec_ref(v___y_1069_);
lean_dec(v___y_1068_);
lean_dec_ref(v___y_1067_);
lean_dec_ref(v_sizes_1060_);
return v_res_1074_;
}
}
static lean_object* _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__3));
v___x_1083_ = l_Lean_mkConst(v___x_1082_, v___x_1081_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0(lean_object* v___x_1087_, lean_object* v___x_1088_, lean_object* v_mvarId_1089_, lean_object* v_sizes_1090_, lean_object* v_hNamePrefix_1091_, lean_object* v_a_1092_, lean_object* v_xNamePrefix_1093_, lean_object* v___y_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_, lean_object* v___y_1097_){
_start:
{
lean_object* v___x_1099_; 
v___x_1099_ = l_Lean_Meta_mkAppM(v___x_1087_, v___x_1088_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1099_) == 0)
{
lean_object* v_a_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_a_1100_ = lean_ctor_get(v___x_1099_, 0);
lean_inc(v_a_1100_);
lean_dec_ref_known(v___x_1099_, 1);
v___x_1101_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__1));
v___x_1102_ = lean_obj_once(&l_Lean_Meta_caseArraySizes___lam__0___closed__4, &l_Lean_Meta_caseArraySizes___lam__0___closed__4_once, _init_l_Lean_Meta_caseArraySizes___lam__0___closed__4);
v___x_1103_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___lam__0___closed__6));
v___x_1104_ = l_Lean_MVarId_assertExt(v_mvarId_1089_, v___x_1101_, v___x_1102_, v_a_1100_, v___x_1103_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1104_) == 0)
{
lean_object* v_a_1105_; uint8_t v___x_1106_; lean_object* v___x_1107_; 
v_a_1105_ = lean_ctor_get(v___x_1104_, 0);
lean_inc(v_a_1105_);
lean_dec_ref_known(v___x_1104_, 1);
v___x_1106_ = 0;
v___x_1107_ = l_Lean_Meta_intro1Core(v_a_1105_, v___x_1106_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1107_) == 0)
{
lean_object* v_a_1108_; lean_object* v_fst_1109_; lean_object* v_snd_1110_; lean_object* v___x_1111_; 
v_a_1108_ = lean_ctor_get(v___x_1107_, 0);
lean_inc(v_a_1108_);
lean_dec_ref_known(v___x_1107_, 1);
v_fst_1109_ = lean_ctor_get(v_a_1108_, 0);
lean_inc(v_fst_1109_);
v_snd_1110_ = lean_ctor_get(v_a_1108_, 1);
lean_inc(v_snd_1110_);
lean_dec(v_a_1108_);
v___x_1111_ = l_Lean_Meta_intro1Core(v_snd_1110_, v___x_1106_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1111_) == 0)
{
lean_object* v_a_1112_; lean_object* v_fst_1113_; lean_object* v_snd_1114_; size_t v_sz_1115_; size_t v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; lean_object* v___x_1119_; 
v_a_1112_ = lean_ctor_get(v___x_1111_, 0);
lean_inc(v_a_1112_);
lean_dec_ref_known(v___x_1111_, 1);
v_fst_1113_ = lean_ctor_get(v_a_1112_, 0);
lean_inc(v_fst_1113_);
v_snd_1114_ = lean_ctor_get(v_a_1112_, 1);
lean_inc(v_snd_1114_);
lean_dec(v_a_1112_);
v_sz_1115_ = lean_array_size(v_sizes_1090_);
v___x_1116_ = ((size_t)0ULL);
lean_inc_ref(v_sizes_1090_);
v___x_1117_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__0(v_sz_1115_, v___x_1116_, v_sizes_1090_);
v___x_1118_ = 1;
v___x_1119_ = l_Lean_Meta_caseValues(v_snd_1114_, v_fst_1109_, v___x_1117_, v_hNamePrefix_1091_, v___x_1118_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
if (lean_obj_tag(v___x_1119_) == 0)
{
lean_object* v_a_1120_; size_t v_sz_1121_; lean_object* v___x_1122_; 
v_a_1120_ = lean_ctor_get(v___x_1119_, 0);
lean_inc(v_a_1120_);
lean_dec_ref_known(v___x_1119_, 1);
v_sz_1121_ = lean_array_size(v_a_1120_);
v___x_1122_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1090_, v_fst_1113_, v_a_1092_, v_xNamePrefix_1093_, v_sz_1121_, v___x_1116_, v_a_1120_, v___y_1094_, v___y_1095_, v___y_1096_, v___y_1097_);
lean_dec_ref(v_sizes_1090_);
return v___x_1122_;
}
else
{
lean_object* v_a_1123_; lean_object* v___x_1125_; uint8_t v_isShared_1126_; uint8_t v_isSharedCheck_1130_; 
lean_dec(v_fst_1113_);
lean_dec(v_xNamePrefix_1093_);
lean_dec_ref(v_a_1092_);
lean_dec_ref(v_sizes_1090_);
v_a_1123_ = lean_ctor_get(v___x_1119_, 0);
v_isSharedCheck_1130_ = !lean_is_exclusive(v___x_1119_);
if (v_isSharedCheck_1130_ == 0)
{
v___x_1125_ = v___x_1119_;
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
else
{
lean_inc(v_a_1123_);
lean_dec(v___x_1119_);
v___x_1125_ = lean_box(0);
v_isShared_1126_ = v_isSharedCheck_1130_;
goto v_resetjp_1124_;
}
v_resetjp_1124_:
{
lean_object* v___x_1128_; 
if (v_isShared_1126_ == 0)
{
v___x_1128_ = v___x_1125_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v_a_1123_);
v___x_1128_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
return v___x_1128_;
}
}
}
}
else
{
lean_object* v_a_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1138_; 
lean_dec(v_fst_1109_);
lean_dec(v_xNamePrefix_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_hNamePrefix_1091_);
lean_dec_ref(v_sizes_1090_);
v_a_1131_ = lean_ctor_get(v___x_1111_, 0);
v_isSharedCheck_1138_ = !lean_is_exclusive(v___x_1111_);
if (v_isSharedCheck_1138_ == 0)
{
v___x_1133_ = v___x_1111_;
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_a_1131_);
lean_dec(v___x_1111_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1138_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v___x_1136_; 
if (v_isShared_1134_ == 0)
{
v___x_1136_ = v___x_1133_;
goto v_reusejp_1135_;
}
else
{
lean_object* v_reuseFailAlloc_1137_; 
v_reuseFailAlloc_1137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1137_, 0, v_a_1131_);
v___x_1136_ = v_reuseFailAlloc_1137_;
goto v_reusejp_1135_;
}
v_reusejp_1135_:
{
return v___x_1136_;
}
}
}
}
else
{
lean_object* v_a_1139_; lean_object* v___x_1141_; uint8_t v_isShared_1142_; uint8_t v_isSharedCheck_1146_; 
lean_dec(v_xNamePrefix_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_hNamePrefix_1091_);
lean_dec_ref(v_sizes_1090_);
v_a_1139_ = lean_ctor_get(v___x_1107_, 0);
v_isSharedCheck_1146_ = !lean_is_exclusive(v___x_1107_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1141_ = v___x_1107_;
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
else
{
lean_inc(v_a_1139_);
lean_dec(v___x_1107_);
v___x_1141_ = lean_box(0);
v_isShared_1142_ = v_isSharedCheck_1146_;
goto v_resetjp_1140_;
}
v_resetjp_1140_:
{
lean_object* v___x_1144_; 
if (v_isShared_1142_ == 0)
{
v___x_1144_ = v___x_1141_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v_a_1139_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
else
{
lean_object* v_a_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1154_; 
lean_dec(v_xNamePrefix_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_hNamePrefix_1091_);
lean_dec_ref(v_sizes_1090_);
v_a_1147_ = lean_ctor_get(v___x_1104_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1104_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1149_ = v___x_1104_;
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_a_1147_);
lean_dec(v___x_1104_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1154_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1150_ == 0)
{
v___x_1152_ = v___x_1149_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v_a_1147_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
else
{
lean_object* v_a_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1162_; 
lean_dec(v_xNamePrefix_1093_);
lean_dec_ref(v_a_1092_);
lean_dec(v_hNamePrefix_1091_);
lean_dec_ref(v_sizes_1090_);
lean_dec(v_mvarId_1089_);
v_a_1155_ = lean_ctor_get(v___x_1099_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v___x_1099_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1157_ = v___x_1099_;
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_a_1155_);
lean_dec(v___x_1099_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1162_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v___x_1160_; 
if (v_isShared_1158_ == 0)
{
v___x_1160_ = v___x_1157_;
goto v_reusejp_1159_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_a_1155_);
v___x_1160_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1159_;
}
v_reusejp_1159_:
{
return v___x_1160_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___lam__0___boxed(lean_object* v___x_1163_, lean_object* v___x_1164_, lean_object* v_mvarId_1165_, lean_object* v_sizes_1166_, lean_object* v_hNamePrefix_1167_, lean_object* v_a_1168_, lean_object* v_xNamePrefix_1169_, lean_object* v___y_1170_, lean_object* v___y_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_, lean_object* v___y_1174_){
_start:
{
lean_object* v_res_1175_; 
v_res_1175_ = l_Lean_Meta_caseArraySizes___lam__0(v___x_1163_, v___x_1164_, v_mvarId_1165_, v_sizes_1166_, v_hNamePrefix_1167_, v_a_1168_, v_xNamePrefix_1169_, v___y_1170_, v___y_1171_, v___y_1172_, v___y_1173_);
lean_dec(v___y_1173_);
lean_dec_ref(v___y_1172_);
lean_dec(v___y_1171_);
lean_dec_ref(v___y_1170_);
return v_res_1175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes(lean_object* v_mvarId_1180_, lean_object* v_fvarId_1181_, lean_object* v_sizes_1182_, lean_object* v_xNamePrefix_1183_, lean_object* v_hNamePrefix_1184_, lean_object* v_a_1185_, lean_object* v_a_1186_, lean_object* v_a_1187_, lean_object* v_a_1188_){
_start:
{
lean_object* v_a_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___f_1195_; lean_object* v___x_1196_; 
v_a_1190_ = l_Lean_mkFVar(v_fvarId_1181_);
v___x_1191_ = ((lean_object*)(l_Lean_Meta_caseArraySizes___closed__1));
v___x_1192_ = lean_unsigned_to_nat(1u);
v___x_1193_ = lean_mk_empty_array_with_capacity(v___x_1192_);
lean_inc_ref(v_a_1190_);
v___x_1194_ = lean_array_push(v___x_1193_, v_a_1190_);
lean_inc(v_mvarId_1180_);
v___f_1195_ = lean_alloc_closure((void*)(l_Lean_Meta_caseArraySizes___lam__0___boxed), 12, 7);
lean_closure_set(v___f_1195_, 0, v___x_1191_);
lean_closure_set(v___f_1195_, 1, v___x_1194_);
lean_closure_set(v___f_1195_, 2, v_mvarId_1180_);
lean_closure_set(v___f_1195_, 3, v_sizes_1182_);
lean_closure_set(v___f_1195_, 4, v_hNamePrefix_1184_);
lean_closure_set(v___f_1195_, 5, v_a_1190_);
lean_closure_set(v___f_1195_, 6, v_xNamePrefix_1183_);
v___x_1196_ = l_Lean_MVarId_withContext___at___00Lean_Meta_caseArraySizes_spec__2___redArg(v_mvarId_1180_, v___f_1195_, v_a_1185_, v_a_1186_, v_a_1187_, v_a_1188_);
return v___x_1196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_caseArraySizes___boxed(lean_object* v_mvarId_1197_, lean_object* v_fvarId_1198_, lean_object* v_sizes_1199_, lean_object* v_xNamePrefix_1200_, lean_object* v_hNamePrefix_1201_, lean_object* v_a_1202_, lean_object* v_a_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_, lean_object* v_a_1206_){
_start:
{
lean_object* v_res_1207_; 
v_res_1207_ = l_Lean_Meta_caseArraySizes(v_mvarId_1197_, v_fvarId_1198_, v_sizes_1199_, v_xNamePrefix_1200_, v_hNamePrefix_1201_, v_a_1202_, v_a_1203_, v_a_1204_, v_a_1205_);
lean_dec(v_a_1205_);
lean_dec_ref(v_a_1204_);
lean_dec(v_a_1203_);
lean_dec_ref(v_a_1202_);
return v_res_1207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3(lean_object* v_sizes_1208_, lean_object* v_fst_1209_, lean_object* v_a_1210_, lean_object* v_xNamePrefix_1211_, lean_object* v_as_1212_, size_t v_sz_1213_, size_t v_i_1214_, lean_object* v_bs_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_){
_start:
{
lean_object* v___x_1221_; 
v___x_1221_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___redArg(v_sizes_1208_, v_fst_1209_, v_a_1210_, v_xNamePrefix_1211_, v_sz_1213_, v_i_1214_, v_bs_1215_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3___boxed(lean_object* v_sizes_1222_, lean_object* v_fst_1223_, lean_object* v_a_1224_, lean_object* v_xNamePrefix_1225_, lean_object* v_as_1226_, lean_object* v_sz_1227_, lean_object* v_i_1228_, lean_object* v_bs_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_){
_start:
{
size_t v_sz_boxed_1235_; size_t v_i_boxed_1236_; lean_object* v_res_1237_; 
v_sz_boxed_1235_ = lean_unbox_usize(v_sz_1227_);
lean_dec(v_sz_1227_);
v_i_boxed_1236_ = lean_unbox_usize(v_i_1228_);
lean_dec(v_i_1228_);
v_res_1237_ = l___private_Init_Data_Array_Basic_0__Array_mapFinIdxMUnsafe_map___at___00Lean_Meta_caseArraySizes_spec__3(v_sizes_1222_, v_fst_1223_, v_a_1224_, v_xNamePrefix_1225_, v_as_1226_, v_sz_boxed_1235_, v_i_boxed_1236_, v_bs_1229_, v___y_1230_, v___y_1231_, v___y_1232_, v___y_1233_);
lean_dec(v___y_1233_);
lean_dec_ref(v___y_1232_);
lean_dec(v___y_1231_);
lean_dec_ref(v___y_1230_);
lean_dec_ref(v_as_1226_);
lean_dec_ref(v_sizes_1222_);
return v_res_1237_;
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
